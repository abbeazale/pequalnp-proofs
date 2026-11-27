import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25504

def rotate (k s w : Nat) := ((w <<< (s % k)) ||| (w >>> (k - s % k))) % 2 ^ k

def bit (k w n : Nat) := w.testBit (n % k)

theorem rotate_bit {k s w : Nat} (hs : s < k) (hw : w < 2 ^ k) (n : Nat) :
    bit k (rotate k s w) (n + s) = bit k w n := by
  have hk : 0 < k := by omega
  have hr := Nat.mod_lt n hk
  have hn : (n+s)%k = (n%k+s)%k := by simp
  unfold bit rotate
  rw [hn]
  simp only [Nat.mod_eq_of_lt hs, Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, decide_eq_true (Nat.mod_lt _ hk), Bool.true_and]
  by_cases h : n%k+s < k
  · rw [Nat.mod_eq_of_lt h]
    have hh : k - s + (n%k+s) = n%k+k := by omega
    have hh' : w.testBit (n%k+k) = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hh, hh']
  · rw [Nat.mod_eq_sub_mod (by omega : k ≤ n%k+s), Nat.mod_eq_of_lt (by omega : n%k+s-k < k)]
    have hh : k-s+(n%k+s-k) = n%k := by omega
    simp [hh, show ¬ n%k+s-k ≥ s by omega]

def pack (f : Nat → Bool) (n : Nat) :=
  (List.range n).foldl (fun a j => a ||| ((f j).toNat <<< j)) 0

theorem pack_bit (f : Nat → Bool) (n i : Nat) :
    (pack f n).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [pack]
  | succ n ih =>
    unfold pack at *
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.testBit_or, ih, Nat.testBit_shiftLeft, Nat.testBit_bool_toNat]
    rcases lt_trichotomy i n with h | h | h
    · simp [h, Nat.lt_succ_of_lt h, show ¬ i ≥ n by omega]
    · subst i
      simp
    · simp [show ¬ i < n by omega, show ¬ i < n+1 by omega, show i-n ≠ 0 by omega]

def chi (k w : Nat) := pack (fun j => xor (w.testBit j)
  (!(w.testBit ((j+1)%k)) && w.testBit ((j+2)%k))) k

theorem chi_lt (k w : Nat) : chi k w < 2^k := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [chi, pack_bit, Nat.not_lt.mpr hi]

def mix (k w : Nat) := w ^^^ rotate k 1 w ^^^ rotate k (k-1) w

def round (k d key con w : Nat) := chi k (mix k w) ^^^ rotate k d key ^^^ con

theorem round_lt {k con : Nat} (hc : con < 2^k) (d key w : Nat) : round k d key con w < 2^k := by
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (chi_lt ..) (Nat.mod_lt _ (Nat.two_pow_pos _))) hc

theorem mix_bit {k w : Nat} (hk : 13 ≤ k) (hw : w < 2^k) (n : Nat) :
    bit k (mix k w) (n+1) = ((bit k w (n+1) ^^ bit k w n) ^^ bit k w (n+2)) := by
  have h := rotate_bit (s := k-1) (by omega : k-1 < k) hw (n+2)
  have he : n+2+(k-1) = (n+1)+k := by omega
  rw [he] at h
  simp only [bit, Nat.add_mod_right] at h
  change ((w ^^^ rotate k 1 w ^^^ rotate k (k-1) w).testBit ((n+1)%k)) = _
  simp only [Nat.testBit_xor]
  rw [h]
  rw [show (rotate k 1 w).testBit ((n+1)%k) = bit k w n from rotate_bit (by omega) hw n]
  rfl

theorem chi_bit {k : Nat} (hk : 0 < k) (w n : Nat) :
    bit k (chi k w) n = xor (bit k w n) (!(bit k w (n+1)) && bit k w (n+2)) := by
  simp [bit, chi, pack_bit, Nat.mod_lt _ hk, Nat.mod_add_mod]

def lin (a b c : Bool) := ((b ^^ a) ^^ c)

theorem round_bit {k w : Nat} (hk : 13 ≤ k) (hw : w < 2^k) (d key con n : Nat) :
    bit k (round k d key con w) (n+1) =
      (((xor (lin (bit k w n) (bit k w (n+1)) (bit k w (n+2)))
        (!(lin (bit k w (n+1)) (bit k w (n+2)) (bit k w (n+3))) &&
          lin (bit k w (n+2)) (bit k w (n+3)) (bit k w (n+4)))) ^^
        bit k (rotate k d key) (n+1)) ^^ bit k con (n+1)) := by
  change ((chi k (mix k w) ^^^ rotate k d key ^^^ con).testBit ((n+1)%k)) = _
  simp only [Nat.testBit_xor]
  rw [show (chi k (mix k w)).testBit ((n+1)%k) = _ from chi_bit (by omega : 0 < k) (mix k w) (n+1)]
  rw [mix_bit hk hw n, mix_bit hk hw (n+1)]
  rw [show bit k (mix k w) (n+1+2) = _ from mix_bit hk hw (n+2)]
  rfl

def init (k row key : Nat) := rotate k 1 key ^^^ row

theorem init_lt {k row : Nat} (hr : row < 2^k) (key : Nat) : init k row key < 2^k :=
  Nat.xor_lt_two_pow (Nat.mod_lt _ (Nat.two_pow_pos _)) hr

theorem key_bit {k key : Nat} (hk : 13 ≤ k) (hw : key < 2^k) (row n : Nat) :
    bit k key n = (bit k (init k row key) (n+1) ^^ bit k row (n+1)) := by
  change _ = (((rotate k 1 key ^^^ row).testBit ((n+1)%k)) ^^ _)
  rw [Nat.testBit_xor, show (rotate k 1 key).testBit ((n+1)%k) = _ from rotate_bit (by omega : 1 < k) hw n]
  simp [bit]

theorem round_pos {k w key d j : Nat} (hk : 13 ≤ k) (hw : w < 2^k) (hy : key < 2^k)
    (hd : d < k) (con row b : Nat) (hj : 0 < j) (hdj : d ≤ j) :
    bit k (round k d key con w) (b+j) =
      (((xor (lin (bit k w (b+(j-1))) (bit k w (b+j)) (bit k w (b+(j+1))))
        (!(lin (bit k w (b+j)) (bit k w (b+(j+1))) (bit k w (b+(j+2)))) &&
          lin (bit k w (b+(j+1))) (bit k w (b+(j+2))) (bit k w (b+(j+3))))) ^^
        (bit k (init k row key) (b+(j-d+1)) ^^ bit k row (b+(j-d+1)))) ^^ bit k con (b+j)) := by
  have h := round_bit hk hw d key con (b+(j-1))
  rw [show b+(j-1)+1 = b+j by omega, show b+(j-1)+2 = b+(j+1) by omega,
    show b+(j-1)+3 = b+(j+2) by omega, show b+(j-1)+4 = b+(j+3) by omega] at h
  have q := rotate_bit hd hy (b+(j-d))
  rw [show b+(j-d)+d = b+j by omega, key_bit hk hy row, Nat.add_assoc] at q
  rw [h, q]

end PEqualNP.Outside.L_meta_25504

open PEqualNP.Outside.L_meta_25504

theorem PEqualNP.Outside.L_meta_25504 : (∀ (k : Nat), 13 ≤ k → ∀ (c : Nat → Fin (2 ^ k))
    (i : Fin k) (u w v z : Fin (2 ^ k)),
  let rot := fun (s word : Nat) =>
    ((word <<< (s % k)) ||| (word >>> (k - s % k))) % 2 ^ k
  let step := fun (word : Nat) =>
    (List.range k).foldl (fun acc j =>
      acc ||| ((xor (word.testBit j)
        (!(word.testBit ((j + 1) % k)) && word.testBit ((j + 2) % k))).toNat <<< j)) 0
  let start := fun (row key : Nat) => rot 1 key ^^^ row
  let first := fun (row key : Nat) =>
    (List.range 3).foldl (fun prev roundIndex =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundIndex) key ^^^ (c (roundIndex + 1)).val)
      (start row key)
  (∀ t : Fin 12, (start u.val w.val).testBit ((i.val + k - 2 + t.val) % k) =
    (start v.val z.val).testBit ((i.val + k - 2 + t.val) % k)) →
  (∀ t : Fin 11, u.val.testBit ((i.val + k - 3 + t.val) % k) =
    v.val.testBit ((i.val + k - 3 + t.val) % k)) →
  (first u.val w.val).testBit i.val = (first v.val z.val).testBit i.val) := by
  intro k hk c i u w v z
  dsimp only
  intro hs hr
  let b := i.val + k - 7
  have hi : (b+7)%k = i.val := by
    rw [show b+7 = i.val+k by dsimp [b]; omega, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
  let s₀ (x y : Fin (2^k)) := init k x.val y.val
  let s₁ (x y : Fin (2^k)) := round k 0 y.val (c 1).val (s₀ x y)
  let s₂ (x y : Fin (2^k)) := round k 2 y.val (c 2).val (s₁ x y)
  let s₃ (x y : Fin (2^k)) := round k 4 y.val (c 3).val (s₂ x y)
  have bound₀ (x y : Fin (2^k)) : s₀ x y < 2^k := init_lt x.isLt _
  have bound₁ (x y : Fin (2^k)) : s₁ x y < 2^k := round_lt (c 1).isLt _ _ _
  have bound₂ (x y : Fin (2^k)) : s₂ x y < 2^k := round_lt (c 2).isLt _ _ _
  change (s₃ u w).testBit i.val = (s₃ v z).testBit i.val
  rw [← hi]
  change bit k (s₃ u w) (b+7) = bit k (s₃ v z) (b+7)
  have h3 (x y : Fin (2^k)) (j : Nat) (hj : 0 < j) (hdj : 4 ≤ j) :=
    round_pos hk (bound₂ x y) y.isLt (by omega : 4 < k) (c 3).val x.val b hj hdj
  simp (disch := decide) only [s₃, h3, Nat.reduceSub, Nat.reduceAdd] 
  have h2 (x y : Fin (2^k)) (j : Nat) (hj : 0 < j) (hdj : 2 ≤ j) :=
    round_pos hk (bound₁ x y) y.isLt (by omega : 2 < k) (c 2).val x.val b hj hdj
  simp (disch := decide) only [s₂, h2, Nat.reduceSub, Nat.reduceAdd] 
  have h1 (x y : Fin (2^k)) (j : Nat) (hj : 0 < j) (hdj : 0 ≤ j) :=
    round_pos hk (bound₀ x y) y.isLt (by omega : 0 < k) (c 1).val x.val b hj hdj
  simp (disch := decide) only [s₁, h1, Nat.reduceSub, Nat.reduceAdd] 
  have startEq (j : Nat) (h₁ : 5 ≤ j) (h₂ : j ≤ 16) :
      bit k (init k u.val w.val) (b+j) = bit k (init k v.val z.val) (b+j) := by
    have h := hs ⟨j-5, by omega⟩
    change bit k (init k u.val w.val) (i.val+k-2+(j-5)) = bit k (init k v.val z.val) _ at h
    rwa [show i.val+k-2+(j-5) = b+j by dsimp [b]; omega] at h
  have rowEq (j : Nat) (h₁ : 4 ≤ j) (h₂ : j ≤ 14) :
      bit k u.val (b+j) = bit k v.val (b+j) := by
    have h := hr ⟨j-4, by omega⟩
    change bit k u.val (i.val+k-3+(j-4)) = bit k v.val _ at h
    rwa [show i.val+k-3+(j-4) = b+j by dsimp [b]; omega] at h
  simp (disch := decide) only [s₀, startEq, rowEq, lin]
  cases h : bit k (init k u.val w.val) (b+4) <;>
    cases h' : bit k (init k v.val z.val) (b+4) <;>
    simp only [Bool.false_xor, Bool.true_xor, Bool.xor_false, Bool.xor_true,
      Bool.not_xor, Bool.xor_not, Bool.not_not]
