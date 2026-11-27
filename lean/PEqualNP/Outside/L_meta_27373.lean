import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_27373_aux

def pm3 (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) ||
  (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6)

def f8 (y : Fin 8 → Bool) : Bool :=
  (y 0 && y 2 && y 7) || (y 0 && y 4 && y 5) || (y 1 && y 2 && y 6) || (y 1 && y 3 && y 5)

def bitsFn (m : ℕ) : Fin 8 → Bool := fun i => m.testBit i.val

def f8b (m : ℕ) : Bool :=
  (m.testBit 0 && m.testBit 2 && m.testBit 7) ||
  (m.testBit 0 && m.testBit 4 && m.testBit 5) ||
  (m.testBit 1 && m.testBit 2 && m.testBit 6) ||
  (m.testBit 1 && m.testBit 3 && m.testBit 5)

theorem f8b_eq_f8 (m : ℕ) : f8b m = f8 (bitsFn m) := rfl

def pop8 (m : ℕ) : ℕ :=
  (if m.testBit 0 then 1 else 0) + (if m.testBit 1 then 1 else 0) +
  (if m.testBit 2 then 1 else 0) + (if m.testBit 3 then 1 else 0) +
  (if m.testBit 4 then 1 else 0) + (if m.testBit 5 then 1 else 0) +
  (if m.testBit 6 then 1 else 0) + (if m.testBit 7 then 1 else 0)

def pack2 (b : Bool) (n : ℕ) : ℕ := 2 * n + b.toNat

theorem pack2_lt (b : Bool) {n k : ℕ} (h : n < k) : pack2 b n < 2 * k := by
  cases b <;> simp [pack2] <;> omega

theorem testBit_pack2_zero (b : Bool) (n : ℕ) : (pack2 b n).testBit 0 = b := by
  cases b <;> simp [pack2, Nat.testBit_zero]

theorem testBit_pack2_succ (b : Bool) (n k : ℕ) : (pack2 b n).testBit (k + 1) = n.testBit k := by
  cases b
  · simp [pack2, Nat.testBit_succ]
  · simp only [pack2, Bool.toNat_true, Nat.testBit_succ, show (2 * n + 1) / 2 = n by omega]

def maskOf (S : Finset (Fin 8)) : ℕ :=
  pack2 (decide ((0 : Fin 8) ∈ S))
    (pack2 (decide ((1 : Fin 8) ∈ S))
      (pack2 (decide ((2 : Fin 8) ∈ S))
        (pack2 (decide ((3 : Fin 8) ∈ S))
          (pack2 (decide ((4 : Fin 8) ∈ S))
            (pack2 (decide ((5 : Fin 8) ∈ S))
              (pack2 (decide ((6 : Fin 8) ∈ S))
                (pack2 (decide ((7 : Fin 8) ∈ S)) 0)))))))

theorem maskOf_lt (S : Finset (Fin 8)) : maskOf S < 256 := by
  unfold maskOf
  exact pack2_lt _ (pack2_lt _ (pack2_lt _ (pack2_lt _ (pack2_lt _ (pack2_lt _ (pack2_lt _ (pack2_lt _ (show 0 < 1 by decide))))))))

theorem testBit_maskOf (S : Finset (Fin 8)) (i : Fin 8) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by
  fin_cases i <;>
    simp only [maskOf, testBit_pack2_zero, testBit_pack2_succ] <;>
    rfl

theorem pop8_maskOf (S : Finset (Fin 8)) : pop8 (maskOf S) = S.card := by
  have hcard : S.card = ∑ i : Fin 8, if i ∈ S then 1 else 0 := by
    simp
  rw [hcard, Fin.sum_univ_eight]
  unfold pop8
  simp only [
    show (maskOf S).testBit 0 = decide ((0 : Fin 8) ∈ S) from testBit_maskOf S 0,
    show (maskOf S).testBit 1 = decide ((1 : Fin 8) ∈ S) from testBit_maskOf S 1,
    show (maskOf S).testBit 2 = decide ((2 : Fin 8) ∈ S) from testBit_maskOf S 2,
    show (maskOf S).testBit 3 = decide ((3 : Fin 8) ∈ S) from testBit_maskOf S 3,
    show (maskOf S).testBit 4 = decide ((4 : Fin 8) ∈ S) from testBit_maskOf S 4,
    show (maskOf S).testBit 5 = decide ((5 : Fin 8) ∈ S) from testBit_maskOf S 5,
    show (maskOf S).testBit 6 = decide ((6 : Fin 8) ∈ S) from testBit_maskOf S 6,
    show (maskOf S).testBit 7 = decide ((7 : Fin 8) ∈ S) from testBit_maskOf S 7,
    decide_eq_true_eq]

theorem maskOf_eq_zero_iff (S : Finset (Fin 8)) : maskOf S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    ext i
    simp only [Finset.notMem_empty, iff_false]
    have hb := testBit_maskOf S i
    rw [h, Nat.zero_testBit] at hb
    simpa using hb.symm
  · rintro rfl
    unfold maskOf pack2
    decide

theorem maskOf_eq_255_iff (S : Finset (Fin 8)) : maskOf S = 255 ↔ S = Finset.univ := by
  constructor
  · intro h
    ext i
    simp only [Finset.mem_univ, iff_true]
    have hb := testBit_maskOf S i
    rw [h] at hb
    have h255 : (255 : ℕ).testBit i.val = true := by fin_cases i <;> decide
    rw [h255] at hb
    simpa using hb.symm
  · rintro rfl
    unfold maskOf pack2
    decide

inductive BTree (α : Type) where
  | leaf (a : α)
  | node (l r : BTree α)

def BTree.get {α : Type} : BTree α → ℕ → ℕ → α
  | BTree.leaf a, _, _ => a
  | BTree.node l _, 0, _ => l.get 0 0
  | BTree.node l r, d + 1, idx =>
      if idx < 2 ^ d then l.get d idx else r.get d (idx - 2 ^ d)

def BTree.check {α : Type} (p : ℕ → α → Bool) : BTree α → ℕ → ℕ → Bool
  | BTree.leaf a, 0, base => p base a
  | BTree.leaf _, _ + 1, _ => false
  | BTree.node _ _, 0, _ => false
  | BTree.node l r, d + 1, base => l.check p d base && r.check p d (base + 2 ^ d)

theorem BTree.check_sound {α : Type} (p : ℕ → α → Bool) (t : BTree α) (d base idx : ℕ)
    (hchk : t.check p d base = true) (hidx : idx < 2 ^ d) :
    p (base + idx) (t.get d idx) = true := by
  induction d generalizing t base idx with
  | zero =>
    cases t with
    | leaf a =>
      simp only [BTree.check] at hchk
      have h0 : idx = 0 := by omega
      subst h0
      simpa [BTree.get] using hchk
    | node l r => simp [BTree.check] at hchk
  | succ d ih =>
    cases t with
    | leaf a => simp [BTree.check] at hchk
    | node l r =>
      simp only [BTree.check, Bool.and_eq_true] at hchk
      simp only [BTree.get]
      split_ifs with hlt
      · exact ih l base idx hchk.1 hlt
      · have h2 : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by ring
        have hrec := ih r (base + 2 ^ d) (idx - 2 ^ d) hchk.2 (by omega)
        simpa [show base + 2 ^ d + (idx - 2 ^ d) = base + idx by omega] using hrec

def orWit : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 133)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0)))))))))
def andWit : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 66) (.leaf 48)) (.node (.leaf 40) (.leaf 41)))) (.node (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 33) (.leaf 33))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34)))) (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 36) (.leaf 37)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 8) (.leaf 9))) (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 12) (.leaf 13)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 4) (.leaf 5))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))))) (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 3) (.leaf 2)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))))) (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 3) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))))))) (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 13) (.leaf 12)) (.node (.leaf 14) (.leaf 14))) (.node (.node (.leaf 9) (.leaf 8)) (.node (.leaf 10) (.leaf 10)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 36) (.leaf 37))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 32) (.leaf 33)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 34) (.leaf 34)))) (.node (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 66))) (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0)))))))))
def modWit : BTree (ℕ × ℕ × ℕ) := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf (0,0,0)) (.leaf (0,0,0))) (.node (.leaf (0,0,0)) (.leaf (2,252,240)))) (.node (.node (.leaf (0,0,0)) (.leaf (4,242,248))) (.node (.leaf (4,233,248)) (.leaf (6,248,176))))) (.node (.node (.node (.leaf (0,0,0)) (.leaf (8,242,244))) (.node (.leaf (2,244,240)) (.leaf (10,244,148)))) (.node (.node (.leaf (8,242,225)) (.leaf (12,242,240))) (.node (.leaf (12,225,240)) (.leaf (14,240,144)))))) (.node (.node (.node (.node (.leaf (0,0,0)) (.leaf (1,236,232))) (.node (.leaf (16,233,236)) (.leaf (18,236,224)))) (.node (.node (.leaf (16,233,226)) (.leaf (20,226,232))) (.node (.leaf (20,233,232)) (.leaf (22,232,160))))) (.node (.node (.node (.leaf (16,227,226)) (.leaf (24,226,228))) (.node (.leaf (24,225,228)) (.leaf (26,228,132)))) (.node (.node (.leaf (24,227,195)) (.leaf (28,226,224))) (.node (.leaf (28,225,224)) (.leaf (30,224,128))))))) (.node (.node (.node (.node (.node (.leaf (0,0,0)) (.leaf (32,218,220))) (.node (.leaf (32,217,220)) (.leaf (34,220,208)))) (.node (.node (.leaf (32,219,210)) (.leaf (36,218,216))) (.node (.leaf (36,217,216)) (.leaf (38,216,144))))) (.node (.node (.node (.leaf (32,211,210)) (.leaf (40,210,212))) (.node (.leaf (40,209,212)) (.leaf (41,212,192)))) (.node (.node (.leaf (40,211,193)) (.leaf (44,210,208))) (.node (.leaf (44,209,208)) (.leaf (45,208,64)))))) (.node (.node (.node (.node (.leaf (32,203,201)) (.leaf (48,202,204))) (.node (.leaf (48,201,204)) (.leaf (50,204,192)))) (.node (.node (.leaf (48,203,194)) (.leaf (52,202,200))) (.node (.leaf (52,201,200)) (.leaf (54,200,128))))) (.node (.node (.node (.leaf (48,195,194)) (.leaf (56,194,196))) (.node (.leaf (56,193,196)) (.leaf (50,196,192)))) (.node (.node (.leaf (52,195,130)) (.leaf (60,194,192))) (.node (.leaf (60,193,192)) (.leaf (54,192,128)))))))) (.node (.node (.node (.node (.node (.node (.leaf (0,0,0)) (.leaf (64,182,188))) (.node (.leaf (2,188,180)) (.leaf (66,188,176)))) (.node (.node (.leaf (4,169,178)) (.leaf (68,178,184))) (.node (.leaf (68,169,184)) (.leaf (69,184,40))))) (.node (.node (.node (.leaf (64,182,178)) (.leaf (72,182,180))) (.node (.leaf (66,180,176)) (.leaf (73,180,160)))) (.node (.node (.leaf (72,178,161)) (.leaf (76,178,176))) (.node (.leaf (76,161,176)) (.leaf (77,176,32)))))) (.node (.node (.node (.node (.leaf (64,166,169)) (.leaf (80,166,172))) (.node (.leaf (80,169,172)) (.leaf (82,172,160)))) (.node (.node (.leaf (80,169,162)) (.leaf (84,162,168))) (.node (.leaf (84,169,168)) (.leaf (85,168,8))))) (.node (.node (.node (.leaf (80,166,162)) (.leaf (88,166,164))) (.node (.leaf (88,161,164)) (.leaf (89,164,4)))) (.node (.node (.leaf (88,163,131)) (.leaf (92,162,160))) (.node (.leaf (92,161,160)) (.leaf (93,160,0))))))) (.node (.node (.node (.node (.node (.leaf (64,158,155)) (.leaf (96,158,156))) (.node (.leaf (96,153,156)) (.leaf (98,156,144)))) (.node (.node (.leaf (96,155,146)) (.leaf (100,154,152))) (.node (.leaf (100,153,152)) (.leaf (101,152,8))))) (.node (.node (.node (.leaf (96,150,146)) (.leaf (104,150,148))) (.node (.leaf (104,145,148)) (.leaf (105,148,128)))) (.node (.node (.leaf (104,147,129)) (.leaf (108,146,144))) (.node (.leaf (108,145,144)) (.leaf (109,144,0)))))) (.node (.node (.node (.node (.leaf (96,142,137)) (.leaf (112,142,140))) (.node (.leaf (112,137,140)) (.leaf (114,140,128)))) (.node (.node (.leaf (112,139,130)) (.leaf (116,138,136))) (.node (.leaf (116,137,136)) (.leaf (114,136,128))))) (.node (.node (.node (.leaf (112,134,130)) (.leaf (120,134,132))) (.node (.leaf (120,129,132)) (.leaf (114,132,128)))) (.node (.node (.leaf (112,131,130)) (.leaf (124,130,128))) (.node (.leaf (124,129,128)) (.leaf (109,128,0))))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf (0,0,0)) (.leaf (1,124,108))) (.node (.leaf (128,109,124)) (.leaf (130,124,112)))) (.node (.node (.leaf (4,114,105)) (.leaf (132,114,120))) (.node (.leaf (132,105,120)) (.leaf (134,120,48))))) (.node (.node (.node (.leaf (128,101,114)) (.leaf (136,114,116))) (.node (.leaf (136,101,116)) (.leaf (138,116,20)))) (.node (.node (.leaf (136,114,97)) (.leaf (140,114,112))) (.node (.leaf (140,97,112)) (.leaf (142,112,16)))))) (.node (.node (.node (.node (.leaf (128,109,105)) (.leaf (129,108,104))) (.node (.leaf (144,109,108)) (.leaf (146,108,96)))) (.node (.node (.leaf (144,105,98)) (.leaf (148,98,104))) (.node (.leaf (148,105,104)) (.leaf (150,104,32))))) (.node (.node (.node (.leaf (144,101,98)) (.leaf (152,98,100))) (.node (.leaf (152,101,100)) (.leaf (154,100,4)))) (.node (.node (.leaf (152,99,67)) (.leaf (156,98,96))) (.node (.leaf (156,97,96)) (.leaf (158,96,0))))))) (.node (.node (.node (.node (.node (.leaf (128,93,91)) (.leaf (160,90,92))) (.node (.leaf (160,93,92)) (.leaf (162,92,80)))) (.node (.node (.leaf (160,91,82)) (.leaf (164,90,88))) (.node (.leaf (164,89,88)) (.leaf (166,88,16))))) (.node (.node (.node (.leaf (160,85,82)) (.leaf (168,82,84))) (.node (.leaf (168,85,84)) (.leaf (169,84,64)))) (.node (.node (.leaf (168,83,65)) (.leaf (172,82,80))) (.node (.leaf (172,81,80)) (.leaf (169,80,64)))))) (.node (.node (.node (.node (.leaf (160,77,73)) (.leaf (176,74,76))) (.node (.leaf (176,77,76)) (.leaf (178,76,64)))) (.node (.node (.leaf (176,75,66)) (.leaf (180,74,72))) (.node (.leaf (180,73,72)) (.leaf (182,72,0))))) (.node (.node (.node (.leaf (176,69,66)) (.leaf (184,66,68))) (.node (.leaf (184,69,68)) (.leaf (178,68,64)))) (.node (.node (.leaf (180,67,2)) (.leaf (188,66,64))) (.node (.leaf (188,65,64)) (.leaf (182,64,0)))))))) (.node (.node (.node (.node (.node (.node (.leaf (128,45,54)) (.leaf (192,54,60))) (.node (.leaf (192,45,60)) (.leaf (194,60,48)))) (.node (.node (.leaf (132,41,50)) (.leaf (196,50,56))) (.node (.leaf (196,41,56)) (.leaf (195,56,32))))) (.node (.node (.node (.leaf (192,54,50)) (.leaf (200,54,52))) (.node (.leaf (200,37,52)) (.leaf (201,52,32)))) (.node (.node (.leaf (200,50,33)) (.leaf (204,50,48))) (.node (.leaf (204,33,48)) (.leaf (203,48,16)))))) (.node (.node (.node (.node (.leaf (192,45,41)) (.leaf (208,38,44))) (.node (.leaf (208,45,44)) (.leaf (210,44,32)))) (.node (.node (.leaf (208,41,34)) (.leaf (212,34,40))) (.node (.leaf (212,41,40)) (.leaf (211,40,8))))) (.node (.node (.node (.leaf (208,39,34)) (.leaf (216,38,36))) (.node (.leaf (216,37,36)) (.leaf (210,36,32)))) (.node (.node (.leaf (216,35,3)) (.leaf (220,34,32))) (.node (.leaf (220,33,32)) (.leaf (219,32,0))))))) (.node (.node (.node (.node (.node (.leaf (192,31,27)) (.leaf (224,30,28))) (.node (.leaf (224,29,28)) (.leaf (226,28,16)))) (.node (.node (.leaf (224,27,18)) (.leaf (228,26,24))) (.node (.leaf (228,25,24)) (.leaf (227,24,0))))) (.node (.node (.node (.leaf (224,23,18)) (.leaf (232,22,20))) (.node (.leaf (232,21,20)) (.leaf (233,20,0)))) (.node (.node (.leaf (232,19,1)) (.leaf (236,18,16))) (.node (.leaf (236,17,16)) (.leaf (233,16,0)))))) (.node (.node (.node (.node (.leaf (224,15,9)) (.leaf (240,14,12))) (.node (.leaf (240,13,12)) (.leaf (242,12,0)))) (.node (.node (.leaf (240,11,2)) (.leaf (244,10,8))) (.node (.leaf (244,9,8)) (.leaf (242,8,0))))) (.node (.node (.node (.leaf (240,7,2)) (.leaf (248,6,4))) (.node (.leaf (248,5,4)) (.leaf (242,4,0)))) (.node (.node (.leaf (240,3,2)) (.leaf (252,2,0))) (.node (.leaf (252,1,0)) (.leaf (0,0,0))))))))))
def svOr0 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 70) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 70) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 70) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 70) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 70) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 133) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 70) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 70) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 70) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 70) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 49) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 42) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 70) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr1 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 133)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 133)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 133)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 49) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr2 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 133))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr3 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 133)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr4 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 133))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr5 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 70) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 70) (.leaf 49))))) (.node (.node (.node (.node (.leaf 49) (.leaf 133)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 70) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 133) (.leaf 49))))) (.node (.node (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 133)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 70) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 70) (.leaf 49))))) (.node (.node (.node (.node (.leaf 49) (.leaf 133)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 70) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 133) (.leaf 49))))) (.node (.node (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 70)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr6 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 133))))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 133) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svOr7 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))))))) (.node (.node (.node (.node (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 70) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))))) (.node (.node (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 49) (.leaf 49)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))))) (.node (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 49))))) (.node (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 42) (.leaf 42)))) (.node (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 70))) (.node (.node (.leaf 42) (.leaf 42)) (.node (.leaf 49) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd0 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 41) (.leaf 0))) (.node (.node (.leaf 66) (.leaf 0)) (.node (.leaf 41) (.leaf 0)))) (.node (.node (.node (.leaf 34) (.leaf 0)) (.node (.leaf 33) (.leaf 0))) (.node (.node (.leaf 35) (.leaf 0)) (.node (.leaf 33) (.leaf 0))))) (.node (.node (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 33) (.leaf 0))) (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 35) (.leaf 0)))) (.node (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 33) (.leaf 0))) (.node (.node (.leaf 37) (.leaf 0)) (.node (.leaf 37) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 0)) (.node (.leaf 9) (.leaf 0))) (.node (.node (.leaf 14) (.leaf 0)) (.node (.leaf 13) (.leaf 0)))) (.node (.node (.node (.leaf 2) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 0)) (.node (.leaf 5) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0)))) (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 2) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) (.node (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 3) (.leaf 0)) (.node (.leaf 1) (.leaf 0))))) (.node (.node (.node (.node (.leaf 6) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 2) (.leaf 0)) (.node (.leaf 2) (.leaf 0)))) (.node (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 5) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 5) (.leaf 0)))) (.node (.node (.node (.leaf 3) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 7) (.leaf 0)) (.node (.leaf 5) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0)))) (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 7) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 3) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 7) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 7) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 7) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 7) (.leaf 0)))) (.node (.node (.node (.leaf 2) (.leaf 0)) (.node (.leaf 2) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 6) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 3) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 7) (.leaf 0)))) (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 2) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 6) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 5) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 0)) (.node (.leaf 6) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 2) (.leaf 0)))) (.node (.node (.node (.leaf 13) (.leaf 0)) (.node (.leaf 14) (.leaf 0))) (.node (.node (.leaf 9) (.leaf 0)) (.node (.leaf 10) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 0)) (.node (.leaf 37) (.leaf 0))) (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 33) (.leaf 0)))) (.node (.node (.node (.leaf 35) (.leaf 0)) (.node (.leaf 33) (.leaf 0))) (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 33) (.leaf 0))))) (.node (.node (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 35) (.leaf 0))) (.node (.node (.leaf 33) (.leaf 0)) (.node (.leaf 34) (.leaf 0)))) (.node (.node (.node (.leaf 41) (.leaf 0)) (.node (.leaf 66) (.leaf 0))) (.node (.node (.leaf 41) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd1 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 50)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 66) (.leaf 50)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 35) (.leaf 34)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 37) (.leaf 37)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 3) (.leaf 2)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 3) (.leaf 2)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 7) (.leaf 6)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 37)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 35) (.leaf 34)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 50) (.leaf 66)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 50) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd2 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 36) (.leaf 37))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 12) (.leaf 13))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 13) (.leaf 12)) (.node (.leaf 14) (.leaf 14))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 36) (.leaf 37))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd3 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 66) (.leaf 52)) (.node (.leaf 40) (.leaf 41)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 33) (.leaf 33))) (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 37) (.leaf 37)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 8) (.leaf 9))) (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 12) (.leaf 13)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 0) (.leaf 1)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 3) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 13) (.leaf 12)) (.node (.leaf 14) (.leaf 14))) (.node (.node (.leaf 9) (.leaf 8)) (.node (.leaf 10) (.leaf 10)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 37)) (.node (.leaf 36) (.leaf 37))) (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 32) (.leaf 33)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 52) (.leaf 66))) (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd4 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 66) (.leaf 48)) (.node (.leaf 44) (.leaf 45)))) (.node (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 38) (.leaf 38)) (.node (.leaf 36) (.leaf 37))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 8) (.leaf 9))) (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 12) (.leaf 13)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 1))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 0) (.leaf 1))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 3) (.leaf 2)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 13) (.leaf 12)) (.node (.leaf 14) (.leaf 14))) (.node (.node (.leaf 9) (.leaf 8)) (.node (.leaf 10) (.leaf 10))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 38) (.leaf 38))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 34) (.leaf 34)))) (.node (.node (.node (.leaf 45) (.leaf 44)) (.node (.leaf 48) (.leaf 66))) (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd5 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 98) (.leaf 48)) (.node (.leaf 40) (.leaf 41)))) (.node (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 33) (.leaf 33))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34)))) (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 36) (.leaf 37)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 36) (.leaf 37))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 32) (.leaf 33)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 34) (.leaf 34)))) (.node (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 98))) (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd6 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 66) (.leaf 48)) (.node (.leaf 40) (.leaf 41)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 33) (.leaf 33))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34)))) (.node (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 37) (.leaf 37)) (.node (.leaf 36) (.leaf 37)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 11)) (.node (.leaf 8) (.leaf 9))) (.node (.node (.leaf 14) (.leaf 15)) (.node (.leaf 12) (.leaf 13)))) (.node (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 0) (.leaf 1))) (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))))) (.node (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 5) (.leaf 5)))) (.node (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 0) (.leaf 1))) (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 4) (.leaf 5))))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 1) (.leaf 1)))) (.node (.node (.node (.leaf 5) (.leaf 5)) (.node (.leaf 5) (.leaf 5))) (.node (.node (.leaf 1) (.leaf 1)) (.node (.leaf 1) (.leaf 1))))) (.node (.node (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6))) (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 3) (.leaf 2)))) (.node (.node (.node (.leaf 13) (.leaf 12)) (.node (.leaf 15) (.leaf 14))) (.node (.node (.leaf 9) (.leaf 8)) (.node (.leaf 11) (.leaf 10)))))) (.node (.node (.node (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 37) (.leaf 37))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 33) (.leaf 33)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 33) (.leaf 33)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34)))) (.node (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 66))) (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))
def svAnd7 : BTree ℕ := (.node (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 48)) (.node (.leaf 40) (.leaf 41))) (.node (.node (.leaf 66) (.leaf 48)) (.node (.leaf 40) (.leaf 41)))) (.node (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34)))) (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 34) (.leaf 34))) (.node (.node (.leaf 37) (.leaf 36)) (.node (.leaf 38) (.leaf 38)))))) (.node (.node (.node (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 10) (.leaf 10))) (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 14) (.leaf 14)))) (.node (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 6) (.leaf 6))))) (.node (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 3) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 7) (.leaf 6)))) (.node (.node (.node (.leaf 1) (.leaf 0)) (.node (.leaf 2) (.leaf 2))) (.node (.node (.leaf 5) (.leaf 4)) (.node (.leaf 6) (.leaf 6))))))) (.node (.node (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 0) (.leaf 1)))) (.node (.node (.node (.leaf 6) (.leaf 7)) (.node (.leaf 4) (.leaf 5))) (.node (.node (.leaf 2) (.leaf 3)) (.node (.leaf 0) (.leaf 1))))) (.node (.node (.node (.node (.leaf 6) (.leaf 6)) (.node (.leaf 6) (.leaf 6))) (.node (.node (.leaf 2) (.leaf 2)) (.node (.leaf 2) (.leaf 2)))) (.node (.node (.node (.leaf 14) (.leaf 14)) (.node (.leaf 14) (.leaf 14))) (.node (.node (.leaf 10) (.leaf 10)) (.node (.leaf 10) (.leaf 10)))))) (.node (.node (.node (.node (.node (.leaf 38) (.leaf 38)) (.node (.leaf 36) (.leaf 37))) (.node (.node (.leaf 34) (.leaf 34)) (.node (.leaf 32) (.leaf 33)))) (.node (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))) (.node (.node (.leaf 34) (.leaf 35)) (.node (.leaf 32) (.leaf 33))))) (.node (.node (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 35) (.leaf 34))) (.node (.node (.leaf 33) (.leaf 32)) (.node (.leaf 34) (.leaf 34)))) (.node (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 66))) (.node (.node (.leaf 41) (.leaf 40)) (.node (.leaf 48) (.leaf 0)))))))) (.node (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))))) (.node (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))) (.node (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))))) (.node (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))) (.node (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0))) (.node (.node (.leaf 0) (.leaf 0)) (.node (.leaf 0) (.leaf 0)))))))))

def pOrWit (L m : ℕ) : Bool :=
  if L == 0 || L == 255 then true
  else f8b m != (f8b (m &&& L) || f8b (m &&& (255 ^^^ L)))

def pAndWit (L m : ℕ) : Bool :=
  if L == 0 || L == 255 then true
  else f8b m != (f8b ((m &&& L) ||| (255 ^^^ L)) && f8b ((m &&& (255 ^^^ L)) ||| L))

def pModWit (S : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  if pop8 S < 2 || 7 < pop8 S then true
  else
    ((t.1 &&& (255 ^^^ S)) == 0) &&
    ((t.2.1 &&& S) == 0) &&
    ((t.2.2 &&& S) == 0) &&
    (f8b (t.1 ||| t.2.1) != f8b t.2.1) &&
    (f8b (t.1 ||| t.2.2) != f8b (S ||| t.2.2))

def pSvOr (s L m : ℕ) : Bool :=
  if L.testBit s || L == 0 || L == (255 ^^^ (1 <<< s)) then true
  else
    let sb := m &&& (1 <<< s)
    let R := (255 ^^^ (1 <<< s)) ^^^ L
    f8b m != (f8b ((m &&& L) ||| sb) || f8b ((m &&& R) ||| sb))

def pSvAnd (s L m : ℕ) : Bool :=
  if L.testBit s || L == 0 || L == (255 ^^^ (1 <<< s)) then true
  else
    let sb := m &&& (1 <<< s)
    let R := (255 ^^^ (1 <<< s)) ^^^ L
    f8b m != (f8b ((m &&& L) ||| R ||| sb) && f8b ((m &&& R) ||| L ||| sb))

theorem orWit_ok : orWit.check pOrWit 8 0 = true := by decide
theorem andWit_ok : andWit.check pAndWit 8 0 = true := by decide
theorem modWit_ok : modWit.check pModWit 8 0 = true := by decide

def svOrTree (s : Fin 8) : BTree ℕ :=
  match s.val with
  | 0 => svOr0 | 1 => svOr1 | 2 => svOr2 | 3 => svOr3
  | 4 => svOr4 | 5 => svOr5 | 6 => svOr6 | _ => svOr7

def svAndTree (s : Fin 8) : BTree ℕ :=
  match s.val with
  | 0 => svAnd0 | 1 => svAnd1 | 2 => svAnd2 | 3 => svAnd3
  | 4 => svAnd4 | 5 => svAnd5 | 6 => svAnd6 | _ => svAnd7

theorem svOr_ok (s : Fin 8) : (svOrTree s).check (pSvOr s.val) 8 0 = true := by fin_cases s <;> decide
theorem svAnd_ok (s : Fin 8) : (svAndTree s).check (pSvAnd s.val) 8 0 = true := by fin_cases s <;> decide

theorem testBit_255 (i : Fin 8) : (255 : ℕ).testBit i.val = true := by
  fin_cases i <;> decide

theorem testBit_one_shift (s i : Fin 8) : (1 <<< s.val).testBit i.val = decide (i = s) := by
  fin_cases s <;> fin_cases i <;> decide

theorem f8_essential (i : Fin 8) : ∃ y : Fin 8 → Bool, f8 y ≠ f8 (Function.update y i (!y i)) := by
  fin_cases i
  · exact ⟨![false, false, true, false, false, false, false, true], by decide⟩
  · exact ⟨![false, false, true, false, false, false, true, false], by decide⟩
  · exact ⟨![true, false, false, false, false, false, false, true], by decide⟩
  · exact ⟨![false, true, false, false, false, true, false, false], by decide⟩
  · exact ⟨![true, false, false, false, false, true, false, false], by decide⟩
  · exact ⟨![true, false, false, false, true, false, false, false], by decide⟩
  · exact ⟨![false, true, true, false, false, false, false, false], by decide⟩
  · exact ⟨![true, false, true, false, false, false, false, false], by decide⟩

theorem f8_no_disjoint_or (L : Finset (Fin 8)) (hne : L.Nonempty) (hnu : L ≠ Finset.univ)
    (A B : (Fin 8 → Bool) → Bool)
    (hA : ∀ y z, (∀ i ∈ L, y i = z i) → A y = A z)
    (hB : ∀ y z, (∀ i ∉ L, y i = z i) → B y = B z)
    (hf : ∀ y, f8 y = (A y || B y)) : False := by
  have h0 : f8 (fun _ => false) = false := by decide
  rw [hf] at h0
  have hA0 : A (fun _ => false) = false := (Bool.or_eq_false_iff.mp h0).1
  have hB0 : B (fun _ => false) = false := (Bool.or_eq_false_iff.mp h0).2
  have hL0 : maskOf L ≠ 0 := fun h => hne.ne_empty ((maskOf_eq_zero_iff L).mp h)
  have hL255 : maskOf L ≠ 255 := fun h => hnu ((maskOf_eq_255_iff L).mp h)
  have hw := BTree.check_sound pOrWit orWit 8 0 (maskOf L) orWit_ok (maskOf_lt L)
  simp only [Nat.zero_add, pOrWit, beq_eq_false_iff_ne.mpr hL0, beq_eq_false_iff_ne.mpr hL255,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne] at hw
  set m := orWit.get 8 (maskOf L)
  have h1 : f8 (bitsFn (m &&& maskOf L)) = A (bitsFn m) := by
    rw [hf]
    have ha : A (bitsFn (m &&& maskOf L)) = A (bitsFn m) := hA _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_and, testBit_maskOf, hi]
    have hb : B (bitsFn (m &&& maskOf L)) = B (fun _ => false) := hB _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_and, testBit_maskOf, hi]
    rw [ha, hb, hB0, Bool.or_false]
  have h2 : f8 (bitsFn (m &&& (255 ^^^ maskOf L))) = B (bitsFn m) := by
    rw [hf]
    have ha : A (bitsFn (m &&& (255 ^^^ maskOf L))) = A (fun _ => false) := hA _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi]
    have hb : B (bitsFn (m &&& (255 ^^^ maskOf L))) = B (bitsFn m) := hB _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi]
    rw [ha, hb, hA0, Bool.false_or]
  apply hw
  rw [f8b_eq_f8, f8b_eq_f8, f8b_eq_f8, h1, h2, hf]

theorem f8_no_disjoint_and (L : Finset (Fin 8)) (hne : L.Nonempty) (hnu : L ≠ Finset.univ)
    (A B : (Fin 8 → Bool) → Bool)
    (hA : ∀ y z, (∀ i ∈ L, y i = z i) → A y = A z)
    (hB : ∀ y z, (∀ i ∉ L, y i = z i) → B y = B z)
    (hf : ∀ y, f8 y = (A y && B y)) : False := by
  have h1' : f8 (fun _ => true) = true := by decide
  rw [hf] at h1'
  have hA1 : A (fun _ => true) = true := ((Bool.and_eq_true _ _).mp h1').1
  have hB1 : B (fun _ => true) = true := ((Bool.and_eq_true _ _).mp h1').2
  have hL0 : maskOf L ≠ 0 := fun h => hne.ne_empty ((maskOf_eq_zero_iff L).mp h)
  have hL255 : maskOf L ≠ 255 := fun h => hnu ((maskOf_eq_255_iff L).mp h)
  have hw := BTree.check_sound pAndWit andWit 8 0 (maskOf L) andWit_ok (maskOf_lt L)
  simp only [Nat.zero_add, pAndWit, beq_eq_false_iff_ne.mpr hL0, beq_eq_false_iff_ne.mpr hL255,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne] at hw
  set m := andWit.get 8 (maskOf L)
  have h1 : f8 (bitsFn ((m &&& maskOf L) ||| (255 ^^^ maskOf L))) = A (bitsFn m) := by
    rw [hf]
    have ha : A (bitsFn ((m &&& maskOf L) ||| (255 ^^^ maskOf L))) = A (bitsFn m) := hA _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi]
    have hb : B (bitsFn ((m &&& maskOf L) ||| (255 ^^^ maskOf L))) = B (fun _ => true) := hB _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi]
    rw [ha, hb, hB1, Bool.and_true]
  have h2 : f8 (bitsFn ((m &&& (255 ^^^ maskOf L)) ||| maskOf L)) = B (bitsFn m) := by
    rw [hf]
    have ha : A (bitsFn ((m &&& (255 ^^^ maskOf L)) ||| maskOf L)) = A (fun _ => true) := hA _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi]
    have hb : B (bitsFn ((m &&& (255 ^^^ maskOf L)) ||| maskOf L)) = B (bitsFn m) := hB _ _ fun i hi => by
      simp [bitsFn, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi]
    rw [ha, hb, hA1, Bool.true_and]
  apply hw
  rw [f8b_eq_f8, f8b_eq_f8, f8b_eq_f8, h1, h2, hf]

theorem f8_no_module (S : Finset (Fin 8)) (hlo : 2 ≤ S.card) (hhi : S.card ≤ 7)
    (G : (Fin 8 → Bool) → Bool)
    (hG_dep : ∀ y z, (∀ i ∈ S, y i = z i) → G y = G z)
    (hG_mono : ∀ y z, (∀ i ∈ S, y i = true → z i = true) → G y = true → G z = true)
    (hf_dep : ∀ y z, G y = G z → (∀ i ∉ S, y i = z i) → f8 y = f8 z) : False := by
  have hpop : pop8 (maskOf S) = S.card := pop8_maskOf S
  have hw := BTree.check_sound pModWit modWit 8 0 (maskOf S) modWit_ok (maskOf_lt S)
  simp only [Nat.zero_add, pModWit] at hw
  have hcond : (decide (pop8 (maskOf S) < 2) || decide (7 < pop8 (maskOf S))) = false := by
    simp [show ¬ pop8 (maskOf S) < 2 by omega, show ¬ 7 < pop8 (maskOf S) by omega]
  simp only [hcond, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hw
  rcases hw with ⟨⟨⟨⟨hxs_sub, hc0_disj⟩, hc1_disj⟩, hne0⟩, hne1⟩
  set t := modWit.get 8 (maskOf S)
  have hG01 : G (fun _ => false) = false ∧ G (fun _ => true) = true := by
    cases h0 : G (fun _ => false)
    · cases h1 : G (fun _ => true)
      · exfalso
        have hconst : ∀ y, G y = false := by
          intro y
          cases hy : G y
          · rfl
          · exfalso
            have := hG_mono y (fun _ => true) (fun _ _ _ => rfl) hy
            rw [h1] at this; cases this
        obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
        obtain ⟨y, hy⟩ := f8_essential i0
        apply hy
        refine hf_dep y (Function.update y i0 (!y i0)) (by rw [hconst, hconst]) fun j hj => ?_
        have hji : j ≠ i0 := fun h => hj (h ▸ hi0)
        simp [Function.update_of_ne hji]
      · exact ⟨rfl, rfl⟩
    · exfalso
      have hconst : ∀ y, G y = true := fun y => hG_mono (fun _ => false) y (fun _ _ h => by cases h) h0
      obtain ⟨i0, hi0⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
      obtain ⟨y, hy⟩ := f8_essential i0
      apply hy
      refine hf_dep y (Function.update y i0 (!y i0)) (by rw [hconst, hconst]) fun j hj => ?_
      have hji : j ≠ i0 := fun h => hj (h ▸ hi0)
      simp [Function.update_of_ne hji]
  cases hGt : G (bitsFn t.1)
  · apply hne0
    rw [f8b_eq_f8, f8b_eq_f8]
    refine hf_dep (bitsFn (t.1 ||| t.2.1)) (bitsFn t.2.1) ?_ ?_
    · have h1 : G (bitsFn (t.1 ||| t.2.1)) = G (bitsFn t.1) := hG_dep _ _ fun i hi => by
        have hc : t.2.1.testBit i.val = false := by
          have hb := congrArg (fun n => n.testBit i.val) hc0_disj
          simp [Nat.testBit_and, testBit_maskOf, hi] at hb
          exact hb
        simp [bitsFn, Nat.testBit_or, hc]
      have h2 : G (bitsFn t.2.1) = G (fun _ => false) := hG_dep _ _ fun i hi => by
        have hc := congrArg (fun n => n.testBit i.val) hc0_disj
        simp [Nat.testBit_and, testBit_maskOf, hi] at hc
        simp [bitsFn, hc]
      rw [h1, h2, hGt, hG01.1]
    · intro i hi
      have hx : t.1.testBit i.val = false := by
        have hb := congrArg (fun n => n.testBit i.val) hxs_sub
        simp [Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi] at hb
        exact hb
      simp [bitsFn, Nat.testBit_or, hx]
  · apply hne1
    rw [f8b_eq_f8, f8b_eq_f8]
    refine hf_dep (bitsFn (t.1 ||| t.2.2)) (bitsFn (maskOf S ||| t.2.2)) ?_ ?_
    · have h1 : G (bitsFn (t.1 ||| t.2.2)) = G (bitsFn t.1) := hG_dep _ _ fun i hi => by
        have hc : t.2.2.testBit i.val = false := by
          have hb := congrArg (fun n => n.testBit i.val) hc1_disj
          simp [Nat.testBit_and, testBit_maskOf, hi] at hb
          exact hb
        simp [bitsFn, Nat.testBit_or, hc]
      have h2 : G (bitsFn (maskOf S ||| t.2.2)) = G (fun _ => true) := hG_dep _ _ fun i hi => by
        simp [bitsFn, Nat.testBit_or, testBit_maskOf, hi]
      rw [h1, h2, hGt, hG01.2]
    · intro i hi
      have hx : t.1.testBit i.val = false := by
        have hb := congrArg (fun n => n.testBit i.val) hxs_sub
        simp [Nat.testBit_and, Nat.testBit_xor, testBit_255, testBit_maskOf, hi] at hb
        exact hb
      simp [bitsFn, Nat.testBit_or, testBit_maskOf, hi, hx]

theorem f8_no_sv_or (s : Fin 8) (L : Finset (Fin 8)) (hsL : s ∉ L)
    (hneL : L.Nonempty) (hneR : (Finset.univ.erase s \ L).Nonempty)
    (A B : (Fin 8 → Bool) → Bool)
    (hA_dep : ∀ y z, y s = z s → (∀ i ∈ L, y i = z i) → A y = A z)
    (hB_dep : ∀ y z, y s = z s → (∀ i, i ≠ s → i ∉ L → y i = z i) → B y = B z)
    (hA_mono : ∀ y z, (∀ i, y i = true → z i = true) → A y = true → A z = true)
    (hB_mono : ∀ y z, (∀ i, y i = true → z i = true) → B y = true → B z = true)
    (hf : ∀ y, f8 y = (A y || B y)) : False := by
  have hbit_s : (maskOf L).testBit s.val = false := by rw [testBit_maskOf]; simp [hsL]
  have hL0 : maskOf L ≠ 0 := fun h => hneL.ne_empty ((maskOf_eq_zero_iff L).mp h)
  have hLfull : maskOf L ≠ 255 ^^^ (1 <<< s.val) := by
    intro heq
    obtain ⟨r, hr⟩ := hneR
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true] at hr
    have hb := congrArg (fun n => n.testBit r.val) heq
    rw [testBit_maskOf, Nat.testBit_xor, testBit_255, testBit_one_shift] at hb
    simp [hr.1, hr.2] at hb
  have hw := BTree.check_sound (pSvOr s.val) (svOrTree s) 8 0 (maskOf L) (svOr_ok s) (maskOf_lt L)
  simp only [Nat.zero_add, pSvOr, hbit_s, beq_eq_false_iff_ne.mpr hL0, beq_eq_false_iff_ne.mpr hLfull,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne] at hw
  set m := (svOrTree s).get 8 (maskOf L)
  set sb := m &&& (1 <<< s.val)
  set R := (255 ^^^ (1 <<< s.val)) ^^^ maskOf L
  have hR_bit : ∀ i : Fin 8, R.testBit i.val = decide (i ≠ s ∧ i ∉ L) := by
    intro i
    simp only [R, Nat.testBit_xor, testBit_255, testBit_one_shift, testBit_maskOf]
    by_cases his : i = s
    · subst his; simp [hsL]
    · by_cases hiL : i ∈ L <;> simp [his, hiL]
  have hA_eq : A (bitsFn ((m &&& maskOf L) ||| sb)) = A (bitsFn m) := by
    refine hA_dep _ _ ?_ fun i hi => ?_
    · simp [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hsL]
    · simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hi, decide_true, Bool.and_true]
      cases m.testBit i.val <;> simp
  have hB_eq : B (bitsFn ((m &&& R) ||| sb)) = B (bitsFn m) := by
    refine hB_dep _ _ ?_ fun i his hiL => ?_
    · simp [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, hR_bit]
    · have hRb : R.testBit i.val = true := by rw [hR_bit]; simp [his, hiL]
      simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, hRb, Bool.and_true]
      cases m.testBit i.val <;> simp
  have hA_le : A (bitsFn ((m &&& R) ||| sb)) = true → A (bitsFn m) = true := fun h =>
    hA_mono _ _ (fun i hi => by
      simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and] at hi ⊢
      rcases Bool.or_eq_true_iff.mp hi with h1 | h1
      · exact ((Bool.and_eq_true _ _).mp h1).1
      · exact ((Bool.and_eq_true _ _).mp h1).1) h
  have hB_le : B (bitsFn ((m &&& maskOf L) ||| sb)) = true → B (bitsFn m) = true := fun h =>
    hB_mono _ _ (fun i hi => by
      simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and] at hi ⊢
      rcases Bool.or_eq_true_iff.mp hi with h1 | h1
      · exact ((Bool.and_eq_true _ _).mp h1).1
      · exact ((Bool.and_eq_true _ _).mp h1).1) h
  apply hw
  rw [f8b_eq_f8, f8b_eq_f8, f8b_eq_f8, hf, hf, hf, hA_eq, hB_eq]
  cases hAm : A (bitsFn m) <;> cases hBm : B (bitsFn m)
  · have h1 : B (bitsFn ((m &&& maskOf L) ||| sb)) = false := by
      cases h : B (bitsFn ((m &&& maskOf L) ||| sb))
      · rfl
      · have := hB_le h; rw [hBm] at this; cases this
    have h2 : A (bitsFn ((m &&& R) ||| sb)) = false := by
      cases h : A (bitsFn ((m &&& R) ||| sb))
      · rfl
      · have := hA_le h; rw [hAm] at this; cases this
    simp [h1, h2]
  · simp
  · simp
  · simp

theorem f8_no_sv_and (s : Fin 8) (L : Finset (Fin 8)) (hsL : s ∉ L)
    (hneL : L.Nonempty) (hneR : (Finset.univ.erase s \ L).Nonempty)
    (A B : (Fin 8 → Bool) → Bool)
    (hA_dep : ∀ y z, y s = z s → (∀ i ∈ L, y i = z i) → A y = A z)
    (hB_dep : ∀ y z, y s = z s → (∀ i, i ≠ s → i ∉ L → y i = z i) → B y = B z)
    (hA_mono : ∀ y z, (∀ i, y i = true → z i = true) → A y = true → A z = true)
    (hB_mono : ∀ y z, (∀ i, y i = true → z i = true) → B y = true → B z = true)
    (hf : ∀ y, f8 y = (A y && B y)) : False := by
  have hbit_s : (maskOf L).testBit s.val = false := by rw [testBit_maskOf]; simp [hsL]
  have hL0 : maskOf L ≠ 0 := fun h => hneL.ne_empty ((maskOf_eq_zero_iff L).mp h)
  have hLfull : maskOf L ≠ 255 ^^^ (1 <<< s.val) := by
    intro heq
    obtain ⟨r, hr⟩ := hneR
    simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_univ, and_true] at hr
    have hb := congrArg (fun n => n.testBit r.val) heq
    rw [testBit_maskOf, Nat.testBit_xor, testBit_255, testBit_one_shift] at hb
    simp [hr.1, hr.2] at hb
  have hw := BTree.check_sound (pSvAnd s.val) (svAndTree s) 8 0 (maskOf L) (svAnd_ok s) (maskOf_lt L)
  simp only [Nat.zero_add, pSvAnd, hbit_s, beq_eq_false_iff_ne.mpr hL0, beq_eq_false_iff_ne.mpr hLfull,
    Bool.or_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne] at hw
  set m := (svAndTree s).get 8 (maskOf L)
  set sb := m &&& (1 <<< s.val)
  set R := (255 ^^^ (1 <<< s.val)) ^^^ maskOf L
  have hR_bit : ∀ i : Fin 8, R.testBit i.val = decide (i ≠ s ∧ i ∉ L) := by
    intro i
    simp only [R, Nat.testBit_xor, testBit_255, testBit_one_shift, testBit_maskOf]
    by_cases his : i = s
    · subst his; simp [hsL]
    · by_cases hiL : i ∈ L <;> simp [his, hiL]
  have hA_eq : A (bitsFn ((m &&& maskOf L) ||| R ||| sb)) = A (bitsFn m) := by
    refine hA_dep _ _ ?_ fun i hi => ?_
    · simp [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hR_bit, hsL]
    · simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hR_bit, hi,
        decide_true, Bool.and_true, not_true_eq_false, and_false, decide_false, Bool.or_false]
      cases m.testBit i.val <;> simp
  have hB_eq : B (bitsFn ((m &&& R) ||| maskOf L ||| sb)) = B (bitsFn m) := by
    refine hB_dep _ _ ?_ fun i his hiL => ?_
    · simp [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hR_bit, hsL]
    · have hRb : R.testBit i.val = true := by rw [hR_bit]; simp [his, hiL]
      have hLb : (maskOf L).testBit i.val = false := by rw [testBit_maskOf]; simp [hiL]
      simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, hRb, hLb, Bool.and_true, Bool.or_false]
      cases m.testBit i.val <;> simp
  have hA_ge : A (bitsFn m) = true → A (bitsFn ((m &&& R) ||| maskOf L ||| sb)) = true := fun h =>
    hA_mono _ _ (fun i hi => by
      simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hR_bit, testBit_one_shift] at hi ⊢
      by_cases his : i = s
      · subst his; simp [hi]
      · by_cases hiL : i ∈ L
        · simp [hiL]
        · simp [his, hiL, hi]) h
  have hB_ge : B (bitsFn m) = true → B (bitsFn ((m &&& maskOf L) ||| R ||| sb)) = true := fun h =>
    hB_mono _ _ (fun i hi => by
      simp only [bitsFn, sb, Nat.testBit_or, Nat.testBit_and, testBit_maskOf, hR_bit, testBit_one_shift] at hi ⊢
      by_cases his : i = s
      · subst his; simp [hi]
      · by_cases hiL : i ∈ L
        · simp [hiL, hi]
        · simp [his, hiL]) h
  apply hw
  rw [f8b_eq_f8, f8b_eq_f8, f8b_eq_f8, hf, hf, hf, hA_eq, hB_eq]
  cases hAm : A (bitsFn m) <;> cases hBm : B (bitsFn m)
  · simp
  · simp
  · simp
  · simp [hA_ge hAm, hB_ge hBm]

inductive Op where
  | and
  | or
  | not
deriving DecidableEq

structure Node where
  op : Op
  a : ℕ
  b : ℕ

structure DAG (m : ℕ) where
  nodes : Fin m → Node
  ha : ∀ j : Fin m, (nodes j).a < 8 + j.val
  hb : ∀ j : Fin m, (nodes j).op ≠ Op.not → (nodes j).b < 8 + j.val

def DAG.val {m : ℕ} (D : DAG m) (y : Fin 8 → Bool) : ℕ → Bool
  | w =>
    if h1 : w < 8 then y ⟨w, h1⟩
    else if h2 : w - 8 < m then
      let nd := D.nodes ⟨w - 8, h2⟩
      have ha : nd.a < w := by
        have h : nd.a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
      match hop : nd.op with
      | Op.not => !(D.val y nd.a)
      | Op.and =>
        have hb : nd.b < w := by
          have h : nd.b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ (by rw [hop]; decide); omega
        D.val y nd.a && D.val y nd.b
      | Op.or =>
        have hb : nd.b < w := by
          have h : nd.b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ (by rw [hop]; decide); omega
        D.val y nd.a || D.val y nd.b
    else false
termination_by w => w

theorem DAG.val_input {m : ℕ} (D : DAG m) (y : Fin 8 → Bool) (i : Fin 8) :
    D.val y i.val = y i := by
  rw [DAG.val]
  simp [i.isLt]

theorem DAG.val_gate_not {m : ℕ} (D : DAG m) (y : Fin 8 → Bool) (j : Fin m)
    (hop : (D.nodes j).op = Op.not) :
    D.val y (8 + j.val) = !(D.val y (D.nodes j).a) := by
  rw [DAG.val]
  have h1 : ¬ 8 + j.val < 8 := by omega
  have h2 : 8 + j.val - 8 < m := by omega
  have hfin : (⟨8 + j.val - 8, h2⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
  simp only [h1, h2, ↓reduceDIte, hfin]
  split <;> simp_all

theorem DAG.val_gate_and {m : ℕ} (D : DAG m) (y : Fin 8 → Bool) (j : Fin m)
    (hop : (D.nodes j).op = Op.and) :
    D.val y (8 + j.val) = (D.val y (D.nodes j).a && D.val y (D.nodes j).b) := by
  rw [DAG.val]
  have h1 : ¬ 8 + j.val < 8 := by omega
  have h2 : 8 + j.val - 8 < m := by omega
  have hfin : (⟨8 + j.val - 8, h2⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
  simp only [h1, h2, ↓reduceDIte, hfin]
  split <;> simp_all

theorem DAG.val_gate_or {m : ℕ} (D : DAG m) (y : Fin 8 → Bool) (j : Fin m)
    (hop : (D.nodes j).op = Op.or) :
    D.val y (8 + j.val) = (D.val y (D.nodes j).a || D.val y (D.nodes j).b) := by
  rw [DAG.val]
  have h1 : ¬ 8 + j.val < 8 := by omega
  have h2 : 8 + j.val - 8 < m := by omega
  have hfin : (⟨8 + j.val - 8, h2⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
  simp only [h1, h2, ↓reduceDIte, hfin]
  split <;> simp_all

def DAG.truncate {m : ℕ} (D : DAG m) (m' : ℕ) (hm' : m' ≤ m) : DAG m' where
  nodes j := D.nodes ⟨j.val, lt_of_lt_of_le j.isLt hm'⟩
  ha j := D.ha ⟨j.val, lt_of_lt_of_le j.isLt hm'⟩
  hb j hop := D.hb ⟨j.val, lt_of_lt_of_le j.isLt hm'⟩ hop

theorem DAG.val_truncate {m : ℕ} (D : DAG m) (m' : ℕ) (hm' : m' ≤ m) (y : Fin 8 → Bool) :
    ∀ w < 8 + m', (D.truncate m' hm').val y w = D.val y w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h1 : w < 8
    · rw [DAG.val_input (D.truncate m' hm') y ⟨w, h1⟩, DAG.val_input D y ⟨w, h1⟩]
    · let j' : Fin m' := ⟨w - 8, by omega⟩
      let j : Fin m := ⟨w - 8, by omega⟩
      have hw_eq : w = 8 + j'.val := by dsimp [j']; omega
      have hnd : (D.truncate m' hm').nodes j' = D.nodes j := rfl
      cases hop : (D.nodes j).op
      · have hop' : ((D.truncate m' hm').nodes j').op = Op.and := by rw [hnd]; exact hop
        rw [hw_eq, DAG.val_gate_and (D.truncate m' hm') y j' hop']
        rw [show 8 + j'.val = 8 + j.val from rfl, DAG.val_gate_and D y j hop, hnd]
        have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
        have hb : (D.nodes j).b < w := hw_eq ▸ D.hb j (by rw [hop]; decide)
        rw [ih _ ha (by omega), ih _ hb (by omega)]
      · have hop' : ((D.truncate m' hm').nodes j').op = Op.or := by rw [hnd]; exact hop
        rw [hw_eq, DAG.val_gate_or (D.truncate m' hm') y j' hop']
        rw [show 8 + j'.val = 8 + j.val from rfl, DAG.val_gate_or D y j hop, hnd]
        have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
        have hb : (D.nodes j).b < w := hw_eq ▸ D.hb j (by rw [hop]; decide)
        rw [ih _ ha (by omega), ih _ hb (by omega)]
      · have hop' : ((D.truncate m' hm').nodes j').op = Op.not := by rw [hnd]; exact hop
        rw [hw_eq, DAG.val_gate_not (D.truncate m' hm') y j' hop']
        rw [show 8 + j'.val = 8 + j.val from rfl, DAG.val_gate_not D y j hop, hnd]
        have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
        rw [ih _ ha (by omega)]

def shiftWire (j0 w0 w : ℕ) : ℕ :=
  if w = 8 + j0 then w0 else if 8 + j0 < w then w - 1 else w

theorem shiftWire_lt {j0 w0 w k : ℕ} (hw0 : w0 < 8 + j0) (hw : w < 8 + k) :
    (k ≤ j0 → shiftWire j0 w0 w < 8 + k) ∧ (j0 < k → shiftWire j0 w0 w < 8 + (k - 1)) := by
  unfold shiftWire
  constructor <;> intro hk <;> split_ifs <;> omega

def DAG.bypass {m : ℕ} (D : DAG m) (j0 : Fin m) (w0 : ℕ) (hw0 : w0 < 8 + j0.val) :
    DAG (m - 1) where
  nodes j :=
    let orig : Fin m := if h : j.val < j0.val then ⟨j.val, by omega⟩ else ⟨j.val + 1, by omega⟩
    let nd := D.nodes orig
    ⟨nd.op, shiftWire j0.val w0 nd.a, shiftWire j0.val w0 nd.b⟩
  ha j := by
    dsimp only
    split_ifs with h
    · exact (shiftWire_lt hw0 (D.ha ⟨j.val, by omega⟩)).1 (le_of_lt h)
    · have h1 : (D.nodes ⟨j.val + 1, by omega⟩).a < 8 + (j.val + 1) := D.ha ⟨j.val + 1, by omega⟩
      have h2 := (shiftWire_lt hw0 h1).2 (by omega)
      omega
  hb j hop := by
    dsimp only at hop ⊢
    split_ifs with h
    · simp only [h, ↓reduceDIte] at hop
      exact (shiftWire_lt hw0 (D.hb ⟨j.val, by omega⟩ hop)).1 (le_of_lt h)
    · simp only [h, ↓reduceDIte] at hop
      have h1 : (D.nodes ⟨j.val + 1, by omega⟩).b < 8 + (j.val + 1) := D.hb ⟨j.val + 1, by omega⟩ hop
      have h2 := (shiftWire_lt hw0 h1).2 (by omega)
      omega

theorem DAG.val_bypass {m : ℕ} (D : DAG m) (j0 : Fin m) (w0 : ℕ) (hw0 : w0 < 8 + j0.val)
    (heq : ∀ y, D.val y (8 + j0.val) = D.val y w0) (y : Fin 8 → Bool) :
    ∀ w < 8 + m, (D.bypass j0 w0 hw0).val y (shiftWire j0.val w0 w) = D.val y w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h1 : w < 8
    · have hsw : shiftWire j0.val w0 w = w := by unfold shiftWire; split_ifs <;> omega
      rw [hsw, DAG.val_input _ y ⟨w, h1⟩, DAG.val_input _ y ⟨w, h1⟩]
    · by_cases hj0 : w = 8 + j0.val
      · subst hj0
        have hsw : shiftWire j0.val w0 (8 + j0.val) = w0 := by unfold shiftWire; simp
        have hsw0 : shiftWire j0.val w0 w0 = w0 := by unfold shiftWire; split_ifs <;> omega
        have hih := ih w0 hw0 (by omega)
        rw [hsw0] at hih
        rw [hsw, heq y, hih]
      · let j : Fin m := ⟨w - 8, by omega⟩
        have hw_eq : w = 8 + j.val := by dsimp [j]; omega
        by_cases hlt : j.val < j0.val
        · have hsw : shiftWire j0.val w0 w = 8 + j.val := by unfold shiftWire; dsimp [j] at hlt ⊢; split_ifs <;> omega
          let j' : Fin (m - 1) := ⟨j.val, by omega⟩
          have hnd : (D.bypass j0 w0 hw0).nodes j' =
              ⟨(D.nodes j).op, shiftWire j0.val w0 (D.nodes j).a, shiftWire j0.val w0 (D.nodes j).b⟩ := by
            simp [DAG.bypass, j', j, hlt]
          rw [hsw]
          cases hop : (D.nodes j).op
          · have hop' : ((D.bypass j0 w0 hw0).nodes j').op = Op.and := by rw [hnd]; exact hop
            rw [show 8 + j.val = 8 + j'.val from rfl, DAG.val_gate_and _ y j' hop', hnd]
            rw [hw_eq, DAG.val_gate_and D y j hop]
            have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
            have hb : (D.nodes j).b < w := hw_eq ▸ D.hb j (by rw [hop]; decide)
            dsimp only
            rw [ih _ ha (by omega), ih _ hb (by omega)]
          · have hop' : ((D.bypass j0 w0 hw0).nodes j').op = Op.or := by rw [hnd]; exact hop
            rw [show 8 + j.val = 8 + j'.val from rfl, DAG.val_gate_or _ y j' hop', hnd]
            rw [hw_eq, DAG.val_gate_or D y j hop]
            have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
            have hb : (D.nodes j).b < w := hw_eq ▸ D.hb j (by rw [hop]; decide)
            dsimp only
            rw [ih _ ha (by omega), ih _ hb (by omega)]
          · have hop' : ((D.bypass j0 w0 hw0).nodes j').op = Op.not := by rw [hnd]; exact hop
            rw [show 8 + j.val = 8 + j'.val from rfl, DAG.val_gate_not _ y j' hop', hnd]
            rw [hw_eq, DAG.val_gate_not D y j hop]
            have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
            dsimp only
            rw [ih _ ha (by omega)]
        · have hgt : j0.val < j.val := by dsimp [j] at hlt ⊢; omega
          have hsw : shiftWire j0.val w0 w = 8 + (j.val - 1) := by unfold shiftWire; dsimp [j] at hgt ⊢; split_ifs <;> omega
          let j' : Fin (m - 1) := ⟨j.val - 1, by omega⟩
          have hnotlt : ¬ j'.val < j0.val := by dsimp [j']; omega
          have hfin : (⟨j'.val + 1, by omega⟩ : Fin m) = j := Fin.ext (by dsimp [j']; omega)
          have hnd : (D.bypass j0 w0 hw0).nodes j' =
              ⟨(D.nodes j).op, shiftWire j0.val w0 (D.nodes j).a, shiftWire j0.val w0 (D.nodes j).b⟩ := by
            simp [DAG.bypass, hnotlt, hfin]
          rw [hsw]
          cases hop : (D.nodes j).op
          · have hop' : ((D.bypass j0 w0 hw0).nodes j').op = Op.and := by rw [hnd]; exact hop
            rw [show 8 + (j.val - 1) = 8 + j'.val from rfl, DAG.val_gate_and _ y j' hop', hnd]
            rw [hw_eq, DAG.val_gate_and D y j hop]
            have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
            have hb : (D.nodes j).b < w := hw_eq ▸ D.hb j (by rw [hop]; decide)
            dsimp only
            rw [ih _ ha (by omega), ih _ hb (by omega)]
          · have hop' : ((D.bypass j0 w0 hw0).nodes j').op = Op.or := by rw [hnd]; exact hop
            rw [show 8 + (j.val - 1) = 8 + j'.val from rfl, DAG.val_gate_or _ y j' hop', hnd]
            rw [hw_eq, DAG.val_gate_or D y j hop]
            have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
            have hb : (D.nodes j).b < w := hw_eq ▸ D.hb j (by rw [hop]; decide)
            dsimp only
            rw [ih _ ha (by omega), ih _ hb (by omega)]
          · have hop' : ((D.bypass j0 w0 hw0).nodes j').op = Op.not := by rw [hnd]; exact hop
            rw [show 8 + (j.val - 1) = 8 + j'.val from rfl, DAG.val_gate_not _ y j' hop', hnd]
            rw [hw_eq, DAG.val_gate_not D y j hop]
            have ha : (D.nodes j).a < w := hw_eq ▸ D.ha j
            dsimp only
            rw [ih _ ha (by omega)]

def DAG.anc {m : ℕ} (D : DAG m) : ℕ → Finset ℕ
  | w =>
    if h1 : w < 8 then {w}
    else if h2 : w - 8 < m then
      let nd := D.nodes ⟨w - 8, h2⟩
      have ha : nd.a < w := by have h : nd.a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
      if hop : nd.op = Op.not then
        insert w (D.anc nd.a)
      else
        have hb : nd.b < w := by have h : nd.b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ hop; omega
        insert w (D.anc nd.a ∪ D.anc nd.b)
    else ∅
termination_by w => w

theorem DAG.anc_gate_not {m : ℕ} (D : DAG m) (j : Fin m) (hop : (D.nodes j).op = Op.not) :
    D.anc (8 + j.val) = insert (8 + j.val) (D.anc (D.nodes j).a) := by
  rw [DAG.anc]
  have h1 : ¬ 8 + j.val < 8 := by omega
  have h2 : 8 + j.val - 8 < m := by omega
  have hfin : (⟨8 + j.val - 8, h2⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
  simp only [h1, h2, ↓reduceDIte, hfin, hop]

theorem DAG.anc_gate_bin {m : ℕ} (D : DAG m) (j : Fin m) (hop : (D.nodes j).op ≠ Op.not) :
    D.anc (8 + j.val) = insert (8 + j.val) (D.anc (D.nodes j).a ∪ D.anc (D.nodes j).b) := by
  rw [DAG.anc]
  have h1 : ¬ 8 + j.val < 8 := by omega
  have h2 : 8 + j.val - 8 < m := by omega
  have hfin : (⟨8 + j.val - 8, h2⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
  simp only [h1, h2, ↓reduceDIte, hfin, hop]

theorem DAG.self_mem_anc {m : ℕ} (D : DAG m) {w : ℕ} (hw : w < 8 + m) : w ∈ D.anc w := by
  rw [DAG.anc]
  by_cases h1 : w < 8
  · simp [h1]
  · have h2 : w - 8 < m := by omega
    simp only [h1, h2, ↓reduceDIte]
    split_ifs <;> simp

theorem DAG.anc_le {m : ℕ} (D : DAG m) : ∀ w u, u ∈ D.anc w → u ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro u hu
    rw [DAG.anc] at hu
    by_cases h1 : w < 8
    · simp only [h1, ↓reduceDIte, Finset.mem_singleton] at hu; omega
    · by_cases h2 : w - 8 < m
      · simp only [h1, h2, ↓reduceDIte] at hu
        split_ifs at hu with hop
        · rcases Finset.mem_insert.mp hu with rfl | hmem
          · exact le_rfl
          · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
              have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
            exact le_of_lt (lt_of_le_of_lt (ih _ ha u hmem) ha)
        · rcases Finset.mem_insert.mp hu with rfl | hmem
          · exact le_rfl
          · rcases Finset.mem_union.mp hmem with hmem | hmem
            · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
                have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
              exact le_of_lt (lt_of_le_of_lt (ih _ ha u hmem) ha)
            · have hb : (D.nodes ⟨w - 8, h2⟩).b < w := by
                have h : (D.nodes ⟨w - 8, h2⟩).b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ hop; omega
              exact le_of_lt (lt_of_le_of_lt (ih _ hb u hmem) hb)
      · simp [h1, h2] at hu

theorem DAG.anc_sub {m : ℕ} (D : DAG m) : ∀ w v, v ∈ D.anc w → D.anc v ⊆ D.anc w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro v hv
    by_cases hvw : v = w
    · subst hvw; exact Finset.Subset.refl _
    · rw [DAG.anc] at hv
      by_cases h1 : w < 8
      · simp only [h1, ↓reduceDIte, Finset.mem_singleton] at hv; exact absurd hv hvw
      · by_cases h2 : w - 8 < m
        · simp only [h1, h2, ↓reduceDIte] at hv
          have hsub : D.anc v ⊆
              (if hop : (D.nodes ⟨w - 8, h2⟩).op = Op.not then D.anc (D.nodes ⟨w - 8, h2⟩).a
               else D.anc (D.nodes ⟨w - 8, h2⟩).a ∪ D.anc (D.nodes ⟨w - 8, h2⟩).b) := by
            split_ifs at hv ⊢ with hop
            · rcases Finset.mem_insert.mp hv with h | h
              · exact absurd h hvw
              · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
                  have hh : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
                exact ih _ ha v h
            · rcases Finset.mem_insert.mp hv with h | h
              · exact absurd h hvw
              · rcases Finset.mem_union.mp h with h | h
                · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
                    have hh : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
                  exact Finset.Subset.trans (ih _ ha v h) Finset.subset_union_left
                · have hb : (D.nodes ⟨w - 8, h2⟩).b < w := by
                    have hh : (D.nodes ⟨w - 8, h2⟩).b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ hop; omega
                  exact Finset.Subset.trans (ih _ hb v h) Finset.subset_union_right
          intro u hu
          rw [DAG.anc]
          simp only [h1, h2, ↓reduceDIte]
          split_ifs with hop
          · simp only [hop, ↓reduceDIte] at hsub
            exact Finset.mem_insert_of_mem (hsub hu)
          · simp only [hop, ↓reduceDIte] at hsub
            exact Finset.mem_insert_of_mem (hsub hu)
        · simp [h1, h2] at hv

theorem DAG.anc_has_input {m : ℕ} (D : DAG m) :
    ∀ w < 8 + m, ∃ i : Fin 8, i.val ∈ D.anc w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases h1 : w < 8
    · exact ⟨⟨w, h1⟩, D.self_mem_anc hw⟩
    · have h2 : w - 8 < m := by omega
      have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
        have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
      obtain ⟨i, hi⟩ := ih _ ha (by omega)
      refine ⟨i, ?_⟩
      rw [DAG.anc]
      simp only [h1, h2, ↓reduceDIte]
      split_ifs
      · exact Finset.mem_insert_of_mem hi
      · exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)

theorem DAG.val_eq_of_agree_anc {m : ℕ} (D : DAG m) (y z : Fin 8 → Bool) :
    ∀ w < 8 + m, (∀ i : Fin 8, i.val ∈ D.anc w → y i = z i) → D.val y w = D.val z w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hagr
    by_cases h1 : w < 8
    · rw [DAG.val_input D y ⟨w, h1⟩, DAG.val_input D z ⟨w, h1⟩]
      exact hagr ⟨w, h1⟩ (D.self_mem_anc hw)
    · let j : Fin m := ⟨w - 8, by omega⟩
      have hw_eq : w = 8 + j.val := by dsimp [j]; omega
      have ha_lt : (D.nodes j).a < w := hw_eq ▸ D.ha j
      cases hop : (D.nodes j).op
      · have hop_ne : (D.nodes j).op ≠ Op.not := by rw [hop]; decide
        have hb_lt : (D.nodes j).b < w := hw_eq ▸ D.hb j hop_ne
        have ha_sub : D.anc (D.nodes j).a ⊆ D.anc w := by
          apply D.anc_sub w; rw [hw_eq, D.anc_gate_bin j hop_ne]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc (by omega)))
        have hb_sub : D.anc (D.nodes j).b ⊆ D.anc w := by
          apply D.anc_sub w; rw [hw_eq, D.anc_gate_bin j hop_ne]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc (by omega)))
        rw [hw_eq, DAG.val_gate_and D y j hop, DAG.val_gate_and D z j hop,
          ih _ ha_lt (by omega) (fun i hi => hagr i (ha_sub hi)),
          ih _ hb_lt (by omega) (fun i hi => hagr i (hb_sub hi))]
      · have hop_ne : (D.nodes j).op ≠ Op.not := by rw [hop]; decide
        have hb_lt : (D.nodes j).b < w := hw_eq ▸ D.hb j hop_ne
        have ha_sub : D.anc (D.nodes j).a ⊆ D.anc w := by
          apply D.anc_sub w; rw [hw_eq, D.anc_gate_bin j hop_ne]
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc (by omega)))
        have hb_sub : D.anc (D.nodes j).b ⊆ D.anc w := by
          apply D.anc_sub w; rw [hw_eq, D.anc_gate_bin j hop_ne]
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc (by omega)))
        rw [hw_eq, DAG.val_gate_or D y j hop, DAG.val_gate_or D z j hop,
          ih _ ha_lt (by omega) (fun i hi => hagr i (ha_sub hi)),
          ih _ hb_lt (by omega) (fun i hi => hagr i (hb_sub hi))]
      · have ha_sub : D.anc (D.nodes j).a ⊆ D.anc w := by
          apply D.anc_sub w; rw [hw_eq, D.anc_gate_not j hop]
          exact Finset.mem_insert_of_mem (D.self_mem_anc (by omega))
        rw [hw_eq, DAG.val_gate_not D y j hop, DAG.val_gate_not D z j hop,
          ih _ ha_lt (by omega) (fun i hi => hagr i (ha_sub hi))]

theorem DAG.val_mono_of_no_not {m : ℕ} (D : DAG m) (y z : Fin 8 → Bool)
    (hle : ∀ i : Fin 8, y i = true → z i = true) :
    ∀ w < 8 + m, (∀ j : Fin m, 8 + j.val ∈ D.anc w → (D.nodes j).op ≠ Op.not) →
    D.val y w = true → D.val z w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hnonot hy
    by_cases h1 : w < 8
    · rw [DAG.val_input D y ⟨w, h1⟩] at hy
      rw [DAG.val_input D z ⟨w, h1⟩]
      exact hle ⟨w, h1⟩ hy
    · let j : Fin m := ⟨w - 8, by omega⟩
      have hw_eq : w = 8 + j.val := by dsimp [j]; omega
      have hne_not : (D.nodes j).op ≠ Op.not := hnonot j (hw_eq ▸ D.self_mem_anc hw)
      have ha_lt : (D.nodes j).a < w := hw_eq ▸ D.ha j
      have hb_lt : (D.nodes j).b < w := hw_eq ▸ D.hb j hne_not
      have ha_sub : D.anc (D.nodes j).a ⊆ D.anc w := by
        apply D.anc_sub w; rw [hw_eq, D.anc_gate_bin j hne_not]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc (by omega)))
      have hb_sub : D.anc (D.nodes j).b ⊆ D.anc w := by
        apply D.anc_sub w; rw [hw_eq, D.anc_gate_bin j hne_not]
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc (by omega)))
      cases hop : (D.nodes j).op
      · rw [hw_eq, DAG.val_gate_and D y j hop, Bool.and_eq_true] at hy
        rw [hw_eq, DAG.val_gate_and D z j hop, Bool.and_eq_true]
        exact ⟨ih _ ha_lt (by omega) (fun k hk => hnonot k (ha_sub hk)) hy.1,
               ih _ hb_lt (by omega) (fun k hk => hnonot k (hb_sub hk)) hy.2⟩
      · rw [hw_eq, DAG.val_gate_or D y j hop, Bool.or_eq_true] at hy
        rw [hw_eq, DAG.val_gate_or D z j hop, Bool.or_eq_true]
        rcases hy with hy | hy
        · exact Or.inl (ih _ ha_lt (by omega) (fun k hk => hnonot k (ha_sub hk)) hy)
        · exact Or.inr (ih _ hb_lt (by omega) (fun k hk => hnonot k (hb_sub hk)) hy)
      · exact absurd hop hne_not

def DAG.uses {m : ℕ} (D : DAG m) (j : Fin m) (w : ℕ) : Prop :=
  (D.nodes j).a = w ∨ ((D.nodes j).op ≠ Op.not ∧ (D.nodes j).b = w)

def DAG.useCount {m : ℕ} (D : DAG m) (j : Fin m) (w : ℕ) : ℕ :=
  (if (D.nodes j).a = w then 1 else 0) +
  (if (D.nodes j).op ≠ Op.not ∧ (D.nodes j).b = w then 1 else 0)

theorem DAG.anc_pred {m : ℕ} (D : DAG m) :
    ∀ v u, u ∈ D.anc v → u ≠ v → ∃ j : Fin m, 8 + j.val ∈ D.anc v ∧ D.uses j u := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro u hu hne
    rw [DAG.anc] at hu
    by_cases h1 : v < 8
    · simp only [h1, ↓reduceDIte, Finset.mem_singleton] at hu; exact absurd hu hne
    · by_cases h2 : v - 8 < m
      · simp only [h1, h2, ↓reduceDIte] at hu
        let j : Fin m := ⟨v - 8, h2⟩
        have hv_eq : 8 + j.val = v := by dsimp [j]; omega
        split_ifs at hu with hop
        · rcases Finset.mem_insert.mp hu with h | h
          · exact absurd h hne
          · by_cases hua : u = (D.nodes j).a
            · exact ⟨j, hv_eq.symm ▸ D.self_mem_anc (by omega), Or.inl hua.symm⟩
            · have ha : (D.nodes j).a < v := hv_eq ▸ D.ha j
              obtain ⟨k, hk_anc, hk_use⟩ := ih _ ha u h hua
              have ha_sub : D.anc (D.nodes j).a ⊆ D.anc v := by
                apply D.anc_sub v; rw [← hv_eq, D.anc_gate_not j hop]
                exact Finset.mem_insert_of_mem (D.self_mem_anc (by omega))
              exact ⟨k, ha_sub hk_anc, hk_use⟩
        · rcases Finset.mem_insert.mp hu with h | h
          · exact absurd h hne
          · rcases Finset.mem_union.mp h with h | h
            · by_cases hua : u = (D.nodes j).a
              · exact ⟨j, hv_eq.symm ▸ D.self_mem_anc (by omega), Or.inl hua.symm⟩
              · have ha : (D.nodes j).a < v := hv_eq ▸ D.ha j
                obtain ⟨k, hk_anc, hk_use⟩ := ih _ ha u h hua
                have ha_sub : D.anc (D.nodes j).a ⊆ D.anc v := by
                  apply D.anc_sub v; rw [← hv_eq, D.anc_gate_bin j hop]
                  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc (by omega)))
                exact ⟨k, ha_sub hk_anc, hk_use⟩
            · by_cases hub : u = (D.nodes j).b
              · exact ⟨j, hv_eq.symm ▸ D.self_mem_anc (by omega), Or.inr ⟨hop, hub.symm⟩⟩
              · have hb : (D.nodes j).b < v := hv_eq ▸ D.hb j hop
                obtain ⟨k, hk_anc, hk_use⟩ := ih _ hb u h hub
                have hb_sub : D.anc (D.nodes j).b ⊆ D.anc v := by
                  apply D.anc_sub v; rw [← hv_eq, D.anc_gate_bin j hop]
                  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc (by omega)))
                exact ⟨k, hb_sub hk_anc, hk_use⟩
      · simp [h1, h2] at hu

def DAG.ancStop {m : ℕ} (D : DAG m) (p : ℕ) : ℕ → Finset ℕ
  | w =>
    if hwp : w = p then {p}
    else if h1 : w < 8 then {w}
    else if h2 : w - 8 < m then
      let nd := D.nodes ⟨w - 8, h2⟩
      have ha : nd.a < w := by have h : nd.a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
      if hop : nd.op = Op.not then
        insert w (D.ancStop p nd.a)
      else
        have hb : nd.b < w := by have h : nd.b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ hop; omega
        insert w (D.ancStop p nd.a ∪ D.ancStop p nd.b)
    else ∅
termination_by w => w

theorem DAG.ancStop_gate_bin {m : ℕ} (D : DAG m) (p : ℕ) (j : Fin m)
    (hne : 8 + j.val ≠ p) (hop : (D.nodes j).op ≠ Op.not) :
    D.ancStop p (8 + j.val) = insert (8 + j.val) (D.ancStop p (D.nodes j).a ∪ D.ancStop p (D.nodes j).b) := by
  rw [DAG.ancStop]
  have h1 : ¬ 8 + j.val < 8 := by omega
  have h2 : 8 + j.val - 8 < m := by omega
  have hfin : (⟨8 + j.val - 8, h2⟩ : Fin m) = j := Fin.ext (by dsimp; omega)
  simp only [hne, h1, h2, ↓reduceDIte, hfin, hop]

theorem DAG.self_mem_ancStop {m : ℕ} (D : DAG m) (p : ℕ) {w : ℕ} (hw : w < 8 + m) :
    w ∈ D.ancStop p w := by
  rw [DAG.ancStop]
  by_cases hwp : w = p
  · simp [hwp]
  · by_cases h1 : w < 8
    · simp [hwp, h1]
    · have h2 : w - 8 < m := by omega
      simp only [hwp, h1, h2, ↓reduceDIte]
      split_ifs <;> simp

theorem DAG.ancStop_le {m : ℕ} (D : DAG m) (p : ℕ) : ∀ w u, u ∈ D.ancStop p w → u ≤ w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro u hu
    rw [DAG.ancStop] at hu
    by_cases hwp : w = p
    · simp only [hwp, ↓reduceDIte, Finset.mem_singleton] at hu; omega
    · by_cases h1 : w < 8
      · simp only [hwp, h1, ↓reduceDIte, Finset.mem_singleton] at hu; omega
      · by_cases h2 : w - 8 < m
        · simp only [hwp, h1, h2, ↓reduceDIte] at hu
          split_ifs at hu with hop
          · rcases Finset.mem_insert.mp hu with rfl | hmem
            · exact le_rfl
            · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
                have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
              exact le_of_lt (lt_of_le_of_lt (ih _ ha u hmem) ha)
          · rcases Finset.mem_insert.mp hu with rfl | hmem
            · exact le_rfl
            · rcases Finset.mem_union.mp hmem with hmem | hmem
              · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
                  have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
                exact le_of_lt (lt_of_le_of_lt (ih _ ha u hmem) ha)
              · have hb : (D.nodes ⟨w - 8, h2⟩).b < w := by
                  have h : (D.nodes ⟨w - 8, h2⟩).b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ hop; omega
                exact le_of_lt (lt_of_le_of_lt (ih _ hb u hmem) hb)
        · simp [hwp, h1, h2] at hu

theorem DAG.ancStop_sub_anc {m : ℕ} (D : DAG m) (p : ℕ) :
    ∀ w < 8 + m, D.ancStop p w ⊆ D.anc w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw u hu
    rw [DAG.ancStop] at hu
    by_cases hwp : w = p
    · simp only [hwp, ↓reduceDIte, Finset.mem_singleton] at hu; subst hu; subst hwp
      exact D.self_mem_anc hw
    · by_cases h1 : w < 8
      · simp only [hwp, h1, ↓reduceDIte, Finset.mem_singleton] at hu; subst hu
        rw [DAG.anc]; simp [h1]
      · have h2 : w - 8 < m := by omega
        simp only [hwp, h1, h2, ↓reduceDIte] at hu
        rw [DAG.anc]; simp only [h1, h2, ↓reduceDIte]
        split_ifs at hu ⊢ with hop
        · rcases Finset.mem_insert.mp hu with rfl | hmem
          · exact Finset.mem_insert_self _ _
          · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
              have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
            exact Finset.mem_insert_of_mem (ih _ ha (by omega) hmem)
        · rcases Finset.mem_insert.mp hu with rfl | hmem
          · exact Finset.mem_insert_self _ _
          · rcases Finset.mem_union.mp hmem with hmem | hmem
            · have ha : (D.nodes ⟨w - 8, h2⟩).a < w := by
                have h : (D.nodes ⟨w - 8, h2⟩).a < 8 + (w - 8) := D.ha ⟨w - 8, h2⟩; omega
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (ih _ ha (by omega) hmem))
            · have hb : (D.nodes ⟨w - 8, h2⟩).b < w := by
                have h : (D.nodes ⟨w - 8, h2⟩).b < 8 + (w - 8) := D.hb ⟨w - 8, h2⟩ hop; omega
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (ih _ hb (by omega) hmem))

theorem DAG.ancStop_pred {m : ℕ} (D : DAG m) (p : ℕ) :
    ∀ v u, u ∈ D.ancStop p v → u ≠ v →
      ∃ j : Fin m, 8 + j.val ∈ D.ancStop p v ∧ 8 + j.val ≠ p ∧ D.uses j u := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro u hu hne
    rw [DAG.ancStop] at hu
    by_cases hvp : v = p
    · simp only [hvp, ↓reduceDIte, Finset.mem_singleton] at hu; omega
    · by_cases h1 : v < 8
      · simp only [hvp, h1, ↓reduceDIte, Finset.mem_singleton] at hu; exact absurd hu hne
      · by_cases h2 : v - 8 < m
        · simp only [hvp, h1, h2, ↓reduceDIte] at hu
          let j : Fin m := ⟨v - 8, h2⟩
          have hv_eq : 8 + j.val = v := by dsimp [j]; omega
          split_ifs at hu with hop
          · rcases Finset.mem_insert.mp hu with h | h
            · exact absurd h hne
            · by_cases hua : u = (D.nodes j).a
              · exact ⟨j, hv_eq.symm ▸ D.self_mem_ancStop p (by omega), hv_eq.symm ▸ hvp, Or.inl hua.symm⟩
              · have ha : (D.nodes j).a < v := hv_eq ▸ D.ha j
                obtain ⟨k, hk_anc, hk_nep, hk_use⟩ := ih _ ha u h hua
                refine ⟨k, ?_, hk_nep, hk_use⟩
                rw [DAG.ancStop]; simp only [hvp, h1, h2, ↓reduceDIte, hop]
                exact Finset.mem_insert_of_mem hk_anc
          · rcases Finset.mem_insert.mp hu with h | h
            · exact absurd h hne
            · rcases Finset.mem_union.mp h with h | h
              · by_cases hua : u = (D.nodes j).a
                · exact ⟨j, hv_eq.symm ▸ D.self_mem_ancStop p (by omega), hv_eq.symm ▸ hvp, Or.inl hua.symm⟩
                · have ha : (D.nodes j).a < v := hv_eq ▸ D.ha j
                  obtain ⟨k, hk_anc, hk_nep, hk_use⟩ := ih _ ha u h hua
                  refine ⟨k, ?_, hk_nep, hk_use⟩
                  rw [DAG.ancStop]; simp only [hvp, h1, h2, ↓reduceDIte, hop]
                  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hk_anc)
              · by_cases hub : u = (D.nodes j).b
                · exact ⟨j, hv_eq.symm ▸ D.self_mem_ancStop p (by omega), hv_eq.symm ▸ hvp, Or.inr ⟨hop, hub.symm⟩⟩
                · have hb : (D.nodes j).b < v := hv_eq ▸ D.hb j hop
                  obtain ⟨k, hk_anc, hk_nep, hk_use⟩ := ih _ hb u h hub
                  refine ⟨k, ?_, hk_nep, hk_use⟩
                  rw [DAG.ancStop]; simp only [hvp, h1, h2, ↓reduceDIte, hop]
                  exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hk_anc)
        · simp [hvp, h1, h2] at hu

theorem DAG.val_eq_of_agree_ancStop {m : ℕ} (D : DAG m) (p : ℕ) (y z : Fin 8 → Bool)
    (hp : D.val y p = D.val z p) :
    ∀ w < 8 + m, (∀ i : Fin 8, i.val ∈ D.ancStop p w → i.val ≠ p → y i = z i) →
    D.val y w = D.val z w := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hagr
    by_cases hwp : w = p
    · subst hwp; exact hp
    · by_cases h1 : w < 8
      · rw [DAG.val_input D y ⟨w, h1⟩, DAG.val_input D z ⟨w, h1⟩]
        exact hagr ⟨w, h1⟩ (D.self_mem_ancStop p hw) hwp
      · let j : Fin m := ⟨w - 8, by omega⟩
        have hw_eq : w = 8 + j.val := by dsimp [j]; omega
        have h2 : w - 8 < m := by omega
        have ha_lt : (D.nodes j).a < w := hw_eq ▸ D.ha j
        cases hop : (D.nodes j).op
        · have hop_ne : (D.nodes j).op ≠ Op.not := by rw [hop]; decide
          have hb_lt : (D.nodes j).b < w := hw_eq ▸ D.hb j hop_ne
          have ha_sub : ∀ i : Fin 8, i.val ∈ D.ancStop p (D.nodes j).a → i.val ∈ D.ancStop p w := fun i hi => by
            rw [hw_eq, D.ancStop_gate_bin p j (hw_eq ▸ hwp) hop_ne]
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)
          have hb_sub : ∀ i : Fin 8, i.val ∈ D.ancStop p (D.nodes j).b → i.val ∈ D.ancStop p w := fun i hi => by
            rw [hw_eq, D.ancStop_gate_bin p j (hw_eq ▸ hwp) hop_ne]
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hi)
          rw [hw_eq, DAG.val_gate_and D y j hop, DAG.val_gate_and D z j hop,
            ih _ ha_lt (by omega) (fun i hi hne => hagr i (ha_sub i hi) hne),
            ih _ hb_lt (by omega) (fun i hi hne => hagr i (hb_sub i hi) hne)]
        · have hop_ne : (D.nodes j).op ≠ Op.not := by rw [hop]; decide
          have hb_lt : (D.nodes j).b < w := hw_eq ▸ D.hb j hop_ne
          have ha_sub : ∀ i : Fin 8, i.val ∈ D.ancStop p (D.nodes j).a → i.val ∈ D.ancStop p w := fun i hi => by
            rw [hw_eq, D.ancStop_gate_bin p j (hw_eq ▸ hwp) hop_ne]
            exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hi)
          have hb_sub : ∀ i : Fin 8, i.val ∈ D.ancStop p (D.nodes j).b → i.val ∈ D.ancStop p w := fun i hi => by
            rw [hw_eq, D.ancStop_gate_bin p j (hw_eq ▸ hwp) hop_ne]
            exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hi)
          rw [hw_eq, DAG.val_gate_or D y j hop, DAG.val_gate_or D z j hop,
            ih _ ha_lt (by omega) (fun i hi hne => hagr i (ha_sub i hi) hne),
            ih _ hb_lt (by omega) (fun i hi hne => hagr i (hb_sub i hi) hne)]
        · have ha_sub : ∀ i : Fin 8, i.val ∈ D.ancStop p (D.nodes j).a → i.val ∈ D.ancStop p w := fun i hi => by
            rw [DAG.ancStop]; simp only [hwp, h1, h2, ↓reduceDIte, show (D.nodes ⟨w - 8, h2⟩).op = Op.not from hop]
            exact Finset.mem_insert_of_mem hi
          rw [hw_eq, DAG.val_gate_not D y j hop, DAG.val_gate_not D z j hop,
            ih _ ha_lt (by omega) (fun i hi hne => hagr i (ha_sub i hi) hne)]

theorem dag_no_le_eight :
    ∀ m ≤ 8, ∀ (D : DAG m) (out : ℕ), out < 8 + m →
      (∀ y : Fin 8 → Bool, D.val y out = f8 y) → False := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro hm8 D out hout hf
    by_cases hout8 : out < 8
    · let i0 : Fin 8 := ⟨out, hout8⟩
      let i1 : Fin 8 := ⟨(out + 1) % 8, Nat.mod_lt _ (by decide)⟩
      have hne : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
      obtain ⟨y, hy⟩ := f8_essential i1
      apply hy
      rw [← hf y, ← hf (Function.update y i1 (!y i1)), DAG.val_input D y i0, DAG.val_input D _ i0]
      simp [Function.update_of_ne hne.symm]
    · by_cases hout_last : out + 1 < 8 + m
      · let m' := out - 7
        have hm' : m' < m := by omega
        have hle' : m' ≤ m := le_of_lt hm'
        refine ih m' hm' (by omega) (D.truncate m' hle') out (by omega) fun y => ?_
        rw [D.val_truncate m' hle' y out (by omega), hf y]
      · have hout_eq : out = 8 + (m - 1) := by omega
        have hm_pos : 0 < m := by omega
        by_cases hdup : ∃ j0 : Fin m, (D.nodes j0).op ≠ Op.not ∧ (D.nodes j0).a = (D.nodes j0).b
        · obtain ⟨j0, hop, hab⟩ := hdup
          have hw0 : (D.nodes j0).a < 8 + j0.val := D.ha j0
          have heq : ∀ y, D.val y (8 + j0.val) = D.val y (D.nodes j0).a := by
            intro y
            cases h : (D.nodes j0).op
            · rw [DAG.val_gate_and D y j0 h, hab, Bool.and_self]
            · rw [DAG.val_gate_or D y j0 h, hab, Bool.or_self]
            · exact absurd h hop
          have hout' : shiftWire j0.val (D.nodes j0).a out < 8 + (m - 1) := by
            have := (shiftWire_lt hw0 (show out < 8 + m by omega)).2 j0.isLt
            exact this
          refine ih (m - 1) (by omega) (by omega) (D.bypass j0 (D.nodes j0).a hw0)
            (shiftWire j0.val (D.nodes j0).a out) hout' fun y => ?_
          rw [D.val_bypass j0 (D.nodes j0).a hw0 heq y out hout, hf y]
        · push Not at hdup
          let Reach := D.anc out
          let Act : Finset (Fin m) := Finset.univ.filter fun j => 8 + j.val ∈ Reach
          let Bin : Finset (Fin m) := Act.filter fun j => (D.nodes j).op ≠ Op.not
          let Un : Finset (Fin m) := Act.filter fun j => (D.nodes j).op = Op.not
          have hAllIn : ∀ i : Fin 8, i.val ∈ Reach := by
            intro i
            by_contra hni
            obtain ⟨y, hy⟩ := f8_essential i
            apply hy
            rw [← hf y, ← hf (Function.update y i (!y i))]
            refine D.val_eq_of_agree_anc y _ out hout fun k hk => ?_
            have hki : k ≠ i := fun h => hni (h ▸ hk)
            simp [Function.update_of_ne hki]
          have hReach_sub : ∀ w ∈ Reach, w < 8 + m := fun w hw =>
            lt_of_le_of_lt (D.anc_le out w hw) hout
          have hReach_card : Reach.card = 8 + Act.card := by
            have hdisj : Disjoint (Finset.range 8) (Act.image fun j : Fin m => 8 + j.val) := by
              rw [Finset.disjoint_left]
              intro w hw1 hw2
              simp only [Finset.mem_range] at hw1
              simp only [Finset.mem_image] at hw2
              rcases hw2 with ⟨j, _, rfl⟩; omega
            have heqR : Reach = Finset.range 8 ∪ Act.image (fun j : Fin m => 8 + j.val) := by
              ext w
              simp only [Finset.mem_union, Finset.mem_range, Finset.mem_image, Act, Finset.mem_filter,
                Finset.mem_univ, true_and]
              constructor
              · intro hw
                by_cases h8 : w < 8
                · exact Or.inl h8
                · have hlt := hReach_sub w hw
                  exact Or.inr ⟨⟨w - 8, by omega⟩, by simpa [show 8 + (w - 8) = w by omega] using hw, by dsimp; omega⟩
              · rintro (h8 | ⟨j, hj, rfl⟩)
                · exact hAllIn ⟨w, h8⟩
                · exact hj
            rw [heqR, Finset.card_union_of_disjoint hdisj, Finset.card_range,
              Finset.card_image_of_injective _ (fun a b h => Fin.ext (by omega))]
          have hAct_split : Act.card = Bin.card + Un.card := by
            have := Finset.card_filter_add_card_filter_not (s := Act) (p := fun j => (D.nodes j).op = Op.not)
            simpa [Bin, Un, Nat.add_comm] using this.symm
          let W := Reach.erase out
          have hout_mem : out ∈ Reach := D.self_mem_anc hout
          have hW_card : W.card = 7 + Bin.card + Un.card := by
            have : W.card = Reach.card - 1 := Finset.card_erase_of_mem hout_mem
            omega
          let cnt (w : ℕ) : ℕ := ∑ j ∈ Act, D.useCount j w
          have hcnt_pos : ∀ w ∈ W, 1 ≤ cnt w := by
            intro w hw
            have hmem := Finset.mem_of_mem_erase hw
            have hne := Finset.ne_of_mem_erase hw
            obtain ⟨j, hj_anc, hj_use⟩ := D.anc_pred out w hmem hne
            have hj_act : j ∈ Act := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_anc⟩
            have h1 : 1 ≤ D.useCount j w := by
              unfold DAG.useCount
              rcases hj_use with ha | ⟨hop, hb⟩
              · simp [ha]
              · simp [hop, hb]
            exact le_trans h1 (Finset.single_le_sum (f := fun j => D.useCount j w) (fun _ _ => Nat.zero_le _) hj_act)
          have hcnt_sum : ∑ w ∈ W, cnt w = 2 * Bin.card + Un.card := by
            simp only [cnt]
            rw [Finset.sum_comm]
            have hgate_sum : ∀ j ∈ Act, (∑ w ∈ W, D.useCount j w) = if (D.nodes j).op = Op.not then 1 else 2 := by
              intro j hj
              have hj_anc : 8 + j.val ∈ Reach := (Finset.mem_filter.mp hj).2
              have ha_mem : (D.nodes j).a ∈ W := by
                refine Finset.mem_erase.mpr ⟨?_, ?_⟩
                · have h1 := D.ha j; have h2 := D.anc_le out (8 + j.val) hj_anc; omega
                · apply D.anc_sub out (8 + j.val) hj_anc
                  by_cases hop : (D.nodes j).op = Op.not
                  · rw [D.anc_gate_not j hop]
                    exact Finset.mem_insert_of_mem (D.self_mem_anc (by have := D.ha j; omega))
                  · rw [D.anc_gate_bin j hop]
                    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc (by have := D.ha j; omega)))
              unfold DAG.useCount
              rw [Finset.sum_add_distrib]
              have hsum_a : (∑ w ∈ W, if (D.nodes j).a = w then 1 else 0) = 1 := by
                simp [ha_mem]
              rw [hsum_a]
              by_cases hop : (D.nodes j).op = Op.not
              · simp [hop]
              · have hb_mem : (D.nodes j).b ∈ W := by
                  refine Finset.mem_erase.mpr ⟨?_, ?_⟩
                  · have h1 := D.hb j hop; have h2 := D.anc_le out (8 + j.val) hj_anc; omega
                  · apply D.anc_sub out (8 + j.val) hj_anc
                    rw [D.anc_gate_bin j hop]
                    exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc (by have := D.hb j hop; omega)))
                have hsum_b : (∑ w ∈ W, if (D.nodes j).op ≠ Op.not ∧ (D.nodes j).b = w then 1 else 0) = 1 := by
                  simp [hop, hb_mem]
                rw [hsum_b]; simp [hop]
            rw [Finset.sum_congr rfl hgate_sum]
            have hsp := Finset.sum_filter_add_sum_filter_not Act (fun j => (D.nodes j).op = Op.not)
              (fun j => if (D.nodes j).op = Op.not then 1 else 2)
            rw [← hsp]
            have h1 : (∑ x ∈ Act.filter (fun j => (D.nodes j).op = Op.not),
                if (D.nodes x).op = Op.not then 1 else 2) = Un.card := by
              calc (∑ x ∈ Act.filter (fun j => (D.nodes j).op = Op.not),
                    if (D.nodes x).op = Op.not then 1 else 2)
                  = ∑ _ ∈ Act.filter (fun j => (D.nodes j).op = Op.not), 1 :=
                    Finset.sum_congr rfl (fun x hx => by simp [(Finset.mem_filter.mp hx).2])
                _ = Un.card := by simp [Un]
            have h2 : (∑ x ∈ Act.filter (fun j => ¬ (D.nodes j).op = Op.not),
                if (D.nodes x).op = Op.not then 1 else 2) = 2 * Bin.card := by
              calc (∑ x ∈ Act.filter (fun j => ¬ (D.nodes j).op = Op.not),
                    if (D.nodes x).op = Op.not then 1 else 2)
                  = ∑ _ ∈ Act.filter (fun j => ¬ (D.nodes j).op = Op.not), 2 :=
                    Finset.sum_congr rfl (fun x hx => by simp [(Finset.mem_filter.mp hx).2])
                _ = 2 * Bin.card := by simp [Bin, mul_comm]
            omega
          have hexcess : (∑ w ∈ W, (cnt w - 1)) = Bin.card - 7 ∧ 7 ≤ Bin.card := by
            have hge : W.card ≤ ∑ w ∈ W, cnt w := by
              calc W.card = ∑ _ ∈ W, 1 := by simp
                _ ≤ ∑ w ∈ W, cnt w := Finset.sum_le_sum hcnt_pos
            have hbin7 : 7 ≤ Bin.card := by omega
            have hadd : (∑ w ∈ W, (cnt w - 1)) + W.card = ∑ w ∈ W, cnt w := by
              calc (∑ w ∈ W, (cnt w - 1)) + W.card
                  = ∑ w ∈ W, ((cnt w - 1) + 1) := by rw [Finset.sum_add_distrib]; simp
                _ = ∑ w ∈ W, cnt w := Finset.sum_congr rfl fun w hw => by have := hcnt_pos w hw; omega
            exact ⟨by omega, hbin7⟩
          have hAct_le : Act.card ≤ 8 := le_trans (Finset.card_le_univ Act |>.trans (by simp)) hm8
          have hcnt_two_of_two_uses : ∀ w ∈ W, ∀ j1 j2 : Fin m, j1 ∈ Act → j2 ∈ Act →
              j1 ≠ j2 → D.uses j1 w → D.uses j2 w → 2 ≤ cnt w := by
            intro w _ j1 j2 hj1 hj2 hne hu1 hu2
            have h1 : 1 ≤ D.useCount j1 w := by
              unfold DAG.useCount
              rcases hu1 with h | ⟨hop, h⟩
              · simp [h]
              · simp [hop, h]
            have h2 : 1 ≤ D.useCount j2 w := by
              unfold DAG.useCount
              rcases hu2 with h | ⟨hop, h⟩
              · simp [h]
              · simp [hop, h]
            have hpair : ({j1, j2} : Finset (Fin m)) ⊆ Act := by
              intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
              rcases hx with rfl | rfl <;> assumption
            have hle := Finset.sum_le_sum_of_subset (f := fun j => D.useCount j w) hpair
            rw [Finset.sum_pair hne] at hle
            dsimp only [cnt]
            omega
          have hmax_common_cnt2 : ∀ c1 c2 : ℕ, c1 ∈ W → c2 ∈ W → c1 ≠ c2 →
              ∀ g : Fin m, g ∈ Act → (D.nodes g).op ≠ Op.not → (D.nodes g).a = c1 → (D.nodes g).b = c2 →
              ∀ S_int : Finset ℕ, S_int = D.anc c1 ∩ D.anc c2 → ∀ (hSne : S_int.Nonempty),
              2 ≤ cnt (S_int.max' hSne) := by
            intro c1 c2 hc1 hc2 hcne g hg hop hga hgb S_int hS hSne
            set w := S_int.max' hSne
            have hw_mem : w ∈ D.anc c1 ∩ D.anc c2 := hS ▸ Finset.max'_mem S_int hSne
            have hw1 : w ∈ D.anc c1 := (Finset.mem_inter.mp hw_mem).1
            have hw2 : w ∈ D.anc c2 := (Finset.mem_inter.mp hw_mem).2
            have hwW : w ∈ W := by
              refine Finset.mem_erase.mpr ⟨?_, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1) hw1⟩
              have h1 := D.anc_le c1 w hw1
              have h2 := D.anc_le out c1 (Finset.mem_of_mem_erase hc1)
              have h3 := Finset.ne_of_mem_erase hc1
              omega
            by_cases hwc1 : w = c1
            · subst hwc1
              have hwc2 : w ≠ c2 := hcne
              obtain ⟨k2, hk2_anc, hk2_use⟩ := D.anc_pred c2 w hw2 hwc2
              have hk2_act : k2 ∈ Act := Finset.mem_filter.mpr
                ⟨Finset.mem_univ _, D.anc_sub out c2 (Finset.mem_of_mem_erase hc2) hk2_anc⟩
              have hk2_ne_g : k2 ≠ g := by
                intro heq; subst heq
                have h1 := D.anc_le c2 (8 + k2.val) hk2_anc
                have h2 := D.hb k2 hop
                omega
              exact hcnt_two_of_two_uses w hwW g k2 hg hk2_act hk2_ne_g.symm (Or.inl hga) hk2_use
            · by_cases hwc2 : w = c2
              · subst hwc2
                obtain ⟨k1, hk1_anc, hk1_use⟩ := D.anc_pred c1 w hw1 hwc1
                have hk1_act : k1 ∈ Act := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1) hk1_anc⟩
                have hk1_ne_g : k1 ≠ g := by
                  intro heq; subst heq
                  have h1 := D.anc_le c1 (8 + k1.val) hk1_anc
                  have h2 := D.ha k1
                  omega
                exact hcnt_two_of_two_uses w hwW g k1 hg hk1_act hk1_ne_g.symm (Or.inr ⟨hop, hgb⟩) hk1_use
              · obtain ⟨k1, hk1_anc, hk1_use⟩ := D.anc_pred c1 w hw1 hwc1
                obtain ⟨k2, hk2_anc, hk2_use⟩ := D.anc_pred c2 w hw2 hwc2
                have hk1_act : k1 ∈ Act := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1) hk1_anc⟩
                have hk2_act : k2 ∈ Act := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, D.anc_sub out c2 (Finset.mem_of_mem_erase hc2) hk2_anc⟩
                have hk_ne : k1 ≠ k2 := by
                  intro heq; subst heq
                  have hmem_int : 8 + k1.val ∈ S_int := hS ▸ Finset.mem_inter.mpr ⟨hk1_anc, hk2_anc⟩
                  have hle_max : 8 + k1.val ≤ w := Finset.le_max' S_int _ hmem_int
                  have hlt_w : w < 8 + k1.val := by
                    rcases hk1_use with ha | ⟨hop1, hb⟩
                    · rw [← ha]; exact D.ha k1
                    · rw [← hb]; exact D.hb k1 hop1
                  omega
                exact hcnt_two_of_two_uses w hwW k1 k2 hk1_act hk2_act hk_ne hk1_use hk2_use
          have hdisj_contra : ∀ (c1 c2 : ℕ), c1 < 8 + m → c2 < 8 + m →
              Disjoint (D.anc c1) (D.anc c2) →
              (∀ i : Fin 8, i.val ∈ D.anc c1 ∨ i.val ∈ D.anc c2) →
              (∀ y, f8 y = (D.val y c1 || D.val y c2)) ∨
              (∀ y, f8 y = (D.val y c1 && D.val y c2)) ∨
              (∀ y, f8 y = (!(D.val y c1) || !(D.val y c2))) ∨
              (∀ y, f8 y = (!(D.val y c1) && !(D.val y c2))) → False := by
            intro c1 c2 hc1 hc2 hdisj hcov hform
            let L : Finset (Fin 8) := Finset.univ.filter fun i => i.val ∈ D.anc c1
            have hneL : L.Nonempty := by
              obtain ⟨i, hi⟩ := D.anc_has_input c1 hc1
              exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
            have hnuL : L ≠ Finset.univ := by
              intro hu
              obtain ⟨i, hi⟩ := D.anc_has_input c2 hc2
              have hiL : i ∈ L := hu ▸ Finset.mem_univ i
              exact Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hiL).2 hi
            have hdep1 : ∀ y z, (∀ i ∈ L, y i = z i) → D.val y c1 = D.val z c1 := fun y z h =>
              D.val_eq_of_agree_anc y z c1 hc1 fun i hi => h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
            have hdep2 : ∀ y z, (∀ i ∉ L, y i = z i) → D.val y c2 = D.val z c2 := fun y z h =>
              D.val_eq_of_agree_anc y z c2 hc2 fun i hi => h i (fun hiL =>
                Finset.disjoint_left.mp hdisj (Finset.mem_filter.mp hiL).2 hi)
            rcases hform with hf' | hf' | hf' | hf'
            · exact f8_no_disjoint_or L hneL hnuL (fun y => D.val y c1) (fun y => D.val y c2) hdep1 hdep2 hf'
            · exact f8_no_disjoint_and L hneL hnuL (fun y => D.val y c1) (fun y => D.val y c2) hdep1 hdep2 hf'
            · exact f8_no_disjoint_or L hneL hnuL (fun y => !(D.val y c1)) (fun y => !(D.val y c2))
                (fun y z h => congrArg Bool.not (hdep1 y z h))
                (fun y z h => congrArg Bool.not (hdep2 y z h)) hf'
            · exact f8_no_disjoint_and L hneL hnuL (fun y => !(D.val y c1)) (fun y => !(D.val y c2))
                (fun y z h => congrArg Bool.not (hdep1 y z h))
                (fun y z h => congrArg Bool.not (hdep2 y z h)) hf'
          let jout : Fin m := ⟨m - 1, by omega⟩
          have hjout_val : out = 8 + jout.val := by dsimp [jout]; omega
          have hjout_act : jout ∈ Act := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hjout_val ▸ hout_mem⟩
          by_cases hBin7 : Bin.card = 7
          · have hcnt1 : ∀ w ∈ W, cnt w = 1 := by
              intro w hw
              have hsum0 : (∑ u ∈ W, (cnt u - 1)) = 0 := by omega
              have h0 := (Finset.sum_eq_zero_iff.mp hsum0) w hw
              have hp := hcnt_pos w hw
              omega
            cases hop_out : (D.nodes jout).op
            · let c1 := (D.nodes jout).a
              let c2 := (D.nodes jout).b
              have hop_ne : (D.nodes jout).op ≠ Op.not := by rw [hop_out]; decide
              have hc1_lt : c1 < 8 + m := lt_trans (D.ha jout) (by omega)
              have hc2_lt : c2 < 8 + m := lt_trans (D.hb jout hop_ne) (by omega)
              have hcne : c1 ≠ c2 := hdup jout hop_ne
              have hc1W : c1 ∈ W := by
                refine Finset.mem_erase.mpr ⟨by have := D.ha jout; omega, ?_⟩
                dsimp only [Reach]; rw [hjout_val, D.anc_gate_bin jout hop_ne]
                exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc hc1_lt))
              have hc2W : c2 ∈ W := by
                refine Finset.mem_erase.mpr ⟨by have := D.hb jout hop_ne; omega, ?_⟩
                dsimp only [Reach]; rw [hjout_val, D.anc_gate_bin jout hop_ne]
                exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc hc2_lt))
              have hdisj : Disjoint (D.anc c1) (D.anc c2) := by
                rw [Finset.disjoint_iff_inter_eq_empty]
                by_contra hne
                have h2 := hmax_common_cnt2 c1 c2 hc1W hc2W hcne jout hjout_act hop_ne rfl rfl
                  (D.anc c1 ∩ D.anc c2) rfl (Finset.nonempty_iff_ne_empty.mpr hne)
                have hwW : (D.anc c1 ∩ D.anc c2).max' (Finset.nonempty_iff_ne_empty.mpr hne) ∈ W := by
                  have hm := (Finset.mem_inter.mp (Finset.max'_mem _ (Finset.nonempty_iff_ne_empty.mpr hne))).1
                  refine Finset.mem_erase.mpr ⟨?_, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) hm⟩
                  have := D.anc_le c1 _ hm; have := D.ha jout; omega
                have h1 := hcnt1 _ hwW; omega
              have hcov : ∀ i : Fin 8, i.val ∈ D.anc c1 ∨ i.val ∈ D.anc c2 := by
                intro i
                have hi := hAllIn i
                dsimp only [Reach] at hi; rw [hjout_val, D.anc_gate_bin jout hop_ne] at hi
                rcases Finset.mem_insert.mp hi with h | h
                · omega
                · exact Finset.mem_union.mp h
              refine hdisj_contra c1 c2 hc1_lt hc2_lt hdisj hcov (Or.inr (Or.inl fun y => ?_))
              rw [← hf y, hjout_val, DAG.val_gate_and D y jout hop_out]
            · let c1 := (D.nodes jout).a
              let c2 := (D.nodes jout).b
              have hop_ne : (D.nodes jout).op ≠ Op.not := by rw [hop_out]; decide
              have hc1_lt : c1 < 8 + m := lt_trans (D.ha jout) (by omega)
              have hc2_lt : c2 < 8 + m := lt_trans (D.hb jout hop_ne) (by omega)
              have hcne : c1 ≠ c2 := hdup jout hop_ne
              have hc1W : c1 ∈ W := by
                refine Finset.mem_erase.mpr ⟨by have := D.ha jout; omega, ?_⟩
                dsimp only [Reach]; rw [hjout_val, D.anc_gate_bin jout hop_ne]
                exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc hc1_lt))
              have hc2W : c2 ∈ W := by
                refine Finset.mem_erase.mpr ⟨by have := D.hb jout hop_ne; omega, ?_⟩
                dsimp only [Reach]; rw [hjout_val, D.anc_gate_bin jout hop_ne]
                exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc hc2_lt))
              have hdisj : Disjoint (D.anc c1) (D.anc c2) := by
                rw [Finset.disjoint_iff_inter_eq_empty]
                by_contra hne
                have h2 := hmax_common_cnt2 c1 c2 hc1W hc2W hcne jout hjout_act hop_ne rfl rfl
                  (D.anc c1 ∩ D.anc c2) rfl (Finset.nonempty_iff_ne_empty.mpr hne)
                have hwW : (D.anc c1 ∩ D.anc c2).max' (Finset.nonempty_iff_ne_empty.mpr hne) ∈ W := by
                  have hm := (Finset.mem_inter.mp (Finset.max'_mem _ (Finset.nonempty_iff_ne_empty.mpr hne))).1
                  refine Finset.mem_erase.mpr ⟨?_, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) hm⟩
                  have := D.anc_le c1 _ hm; have := D.ha jout; omega
                have h1 := hcnt1 _ hwW; omega
              have hcov : ∀ i : Fin 8, i.val ∈ D.anc c1 ∨ i.val ∈ D.anc c2 := by
                intro i
                have hi := hAllIn i
                dsimp only [Reach] at hi; rw [hjout_val, D.anc_gate_bin jout hop_ne] at hi
                rcases Finset.mem_insert.mp hi with h | h
                · omega
                · exact Finset.mem_union.mp h
              refine hdisj_contra c1 c2 hc1_lt hc2_lt hdisj hcov (Or.inl fun y => ?_)
              rw [← hf y, hjout_val, DAG.val_gate_or D y jout hop_out]
            · let c := (D.nodes jout).a
              have hc_lt : c < 8 + jout.val := D.ha jout
              have hc_ge8 : 8 ≤ c := by
                by_contra hc8
                let i0 : Fin 8 := ⟨c, by omega⟩
                let i1 : Fin 8 := ⟨(c + 1) % 8, Nat.mod_lt _ (by decide)⟩
                have hne : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
                obtain ⟨y, hy⟩ := f8_essential i1
                apply hy
                rw [← hf y, ← hf (Function.update y i1 (!y i1)), hjout_val,
                  DAG.val_gate_not D y jout hop_out, DAG.val_gate_not D _ jout hop_out,
                  DAG.val_input D y i0, DAG.val_input D _ i0]
                simp [Function.update_of_ne hne.symm]
              let jc : Fin m := ⟨c - 8, by omega⟩
              have hc_eq : c = 8 + jc.val := by dsimp [jc]; omega
              have hjc_act : jc ∈ Act := by
                refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
                dsimp only [Reach]; rw [← hc_eq, hjout_val, D.anc_gate_not jout hop_out]
                exact Finset.mem_insert_of_mem (D.self_mem_anc (by omega))
              have hUn1 : Un.card ≤ 1 := by omega
              have hjout_Un : jout ∈ Un := Finset.mem_filter.mpr ⟨hjout_act, hop_out⟩
              have hjc_ne_jout : jc ≠ jout := by intro h; have := congrArg Fin.val h; dsimp [jc, jout] at this; omega
              have hop_c_ne : (D.nodes jc).op ≠ Op.not := by
                intro hopc
                have hjc_Un : jc ∈ Un := Finset.mem_filter.mpr ⟨hjc_act, hopc⟩
                have h2 : 2 ≤ Un.card := by
                  calc 2 = ({jout, jc} : Finset (Fin m)).card := (Finset.card_pair hjc_ne_jout.symm).symm
                    _ ≤ Un.card := Finset.card_le_card fun x hx => by
                      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
                      rcases hx with rfl | rfl <;> assumption
                omega
              let c1 := (D.nodes jc).a
              let c2 := (D.nodes jc).b
              have hc1_lt : c1 < 8 + m := lt_trans (D.ha jc) (by omega)
              have hc2_lt : c2 < 8 + m := lt_trans (D.hb jc hop_c_ne) (by omega)
              have hcne : c1 ≠ c2 := hdup jc hop_c_ne
              have hc1W : c1 ∈ W := by
                refine Finset.mem_erase.mpr ⟨by have := D.ha jc; omega, ?_⟩
                apply D.anc_sub out c (by rw [hc_eq]; exact (Finset.mem_filter.mp hjc_act).2)
                rw [hc_eq, D.anc_gate_bin jc hop_c_ne]
                exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc hc1_lt))
              have hc2W : c2 ∈ W := by
                refine Finset.mem_erase.mpr ⟨by have := D.hb jc hop_c_ne; omega, ?_⟩
                apply D.anc_sub out c (by rw [hc_eq]; exact (Finset.mem_filter.mp hjc_act).2)
                rw [hc_eq, D.anc_gate_bin jc hop_c_ne]
                exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc hc2_lt))
              have hdisj : Disjoint (D.anc c1) (D.anc c2) := by
                rw [Finset.disjoint_iff_inter_eq_empty]
                by_contra hne
                have h2 := hmax_common_cnt2 c1 c2 hc1W hc2W hcne jc hjc_act hop_c_ne rfl rfl
                  (D.anc c1 ∩ D.anc c2) rfl (Finset.nonempty_iff_ne_empty.mpr hne)
                have hwW : (D.anc c1 ∩ D.anc c2).max' (Finset.nonempty_iff_ne_empty.mpr hne) ∈ W := by
                  have hm := (Finset.mem_inter.mp (Finset.max'_mem _ (Finset.nonempty_iff_ne_empty.mpr hne))).1
                  refine Finset.mem_erase.mpr ⟨?_, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) hm⟩
                  have := D.anc_le c1 _ hm; have := D.ha jc; omega
                have h1 := hcnt1 _ hwW; omega
              have hcov : ∀ i : Fin 8, i.val ∈ D.anc c1 ∨ i.val ∈ D.anc c2 := by
                intro i
                have hi := hAllIn i
                dsimp only [Reach] at hi; rw [hjout_val, D.anc_gate_not jout hop_out] at hi
                rcases Finset.mem_insert.mp hi with h | hi2
                · omega
                · rw [show (D.nodes jout).a = c from rfl, hc_eq, D.anc_gate_bin jc hop_c_ne] at hi2
                  rcases Finset.mem_insert.mp hi2 with h | h
                  · omega
                  · exact Finset.mem_union.mp h
              cases hopc : (D.nodes jc).op
              · refine hdisj_contra c1 c2 hc1_lt hc2_lt hdisj hcov (Or.inr (Or.inr (Or.inl fun y => ?_)))
                rw [← hf y, hjout_val, DAG.val_gate_not D y jout hop_out, show (D.nodes jout).a = c from rfl, hc_eq, DAG.val_gate_and D y jc hopc, Bool.not_and]
              · refine hdisj_contra c1 c2 hc1_lt hc2_lt hdisj hcov (Or.inr (Or.inr (Or.inr fun y => ?_)))
                rw [← hf y, hjout_val, DAG.val_gate_not D y jout hop_out, show (D.nodes jout).a = c from rfl, hc_eq, DAG.val_gate_or D y jc hopc, Bool.not_or]
              · exact absurd hopc hop_c_ne
          · have hBin8 : Bin.card = 8 := by omega
            have hUn0 : Un.card = 0 := by omega
            have hno_not : ∀ j : Fin m, 8 + j.val ∈ Reach → (D.nodes j).op ≠ Op.not := by
              intro j hj hop
              have : j ∈ Un := Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, hop⟩
              have := Finset.card_pos.mpr ⟨j, this⟩
              omega
            have hmono_all : ∀ w ∈ Reach, ∀ y z : Fin 8 → Bool,
                (∀ i : Fin 8, y i = true → z i = true) → D.val y w = true → D.val z w = true := by
              intro w hw y z hle hy
              exact D.val_mono_of_no_not y z hle w (hReach_sub w hw)
                (fun j hj => hno_not j (D.anc_sub out w hw hj)) hy
            have hex1 : (∑ w ∈ W, (cnt w - 1)) = 1 := by omega
            have hop_out_ne : (D.nodes jout).op ≠ Op.not := hno_not jout (hjout_val ▸ hout_mem)
            let c1 := (D.nodes jout).a
            let c2 := (D.nodes jout).b
            have hc1_lt : c1 < 8 + m := lt_trans (D.ha jout) (by omega)
            have hc2_lt : c2 < 8 + m := lt_trans (D.hb jout hop_out_ne) (by omega)
            have hcne : c1 ≠ c2 := hdup jout hop_out_ne
            have hc1W : c1 ∈ W := by
              refine Finset.mem_erase.mpr ⟨by have := D.ha jout; omega, ?_⟩
              dsimp only [Reach]; rw [hjout_val, D.anc_gate_bin jout hop_out_ne]
              exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (D.self_mem_anc hc1_lt))
            have hc2W : c2 ∈ W := by
              refine Finset.mem_erase.mpr ⟨by have := D.hb jout hop_out_ne; omega, ?_⟩
              dsimp only [Reach]; rw [hjout_val, D.anc_gate_bin jout hop_out_ne]
              exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (D.self_mem_anc hc2_lt))
            have hcov_out : ∀ i : Fin 8, i.val ∈ D.anc c1 ∨ i.val ∈ D.anc c2 := by
              intro i
              have hi := hAllIn i
              dsimp only [Reach] at hi; rw [hjout_val, D.anc_gate_bin jout hop_out_ne] at hi
              rcases Finset.mem_insert.mp hi with h | h
              · omega
              · exact Finset.mem_union.mp h
            by_cases hdisj : Disjoint (D.anc c1) (D.anc c2)
            · cases hopo : (D.nodes jout).op
              · refine hdisj_contra c1 c2 hc1_lt hc2_lt hdisj hcov_out (Or.inr (Or.inl fun y => ?_))
                rw [← hf y, hjout_val, DAG.val_gate_and D y jout hopo]
              · refine hdisj_contra c1 c2 hc1_lt hc2_lt hdisj hcov_out (Or.inl fun y => ?_)
                rw [← hf y, hjout_val, DAG.val_gate_or D y jout hopo]
              · exact absurd hopo hop_out_ne
            · have hne_int : (D.anc c1 ∩ D.anc c2).Nonempty :=
                Finset.nonempty_iff_ne_empty.mpr (fun h => hdisj (Finset.disjoint_iff_inter_eq_empty.mpr h))
              let p := (D.anc c1 ∩ D.anc c2).max' hne_int
              have hp_mem_int : p ∈ D.anc c1 ∩ D.anc c2 := Finset.max'_mem _ hne_int
              have hp1 : p ∈ D.anc c1 := (Finset.mem_inter.mp hp_mem_int).1
              have hp2 : p ∈ D.anc c2 := (Finset.mem_inter.mp hp_mem_int).2
              have hpW : p ∈ W := by
                refine Finset.mem_erase.mpr ⟨?_, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) hp1⟩
                have := D.anc_le c1 p hp1; have := D.ha jout; omega
              have hp_cnt2 : 2 ≤ cnt p :=
                hmax_common_cnt2 c1 c2 hc1W hc2W hcne jout hjout_act hop_out_ne rfl rfl
                  (D.anc c1 ∩ D.anc c2) rfl hne_int
              have hcnt_other : ∀ w ∈ W, w ≠ p → cnt w = 1 := by
                intro w hw hne
                have hsplit := Finset.add_sum_erase W (fun u => cnt u - 1) hpW
                rw [hex1] at hsplit
                have hp1' : 1 ≤ cnt p - 1 := by omega
                have hrest0 : (∑ u ∈ W.erase p, (cnt u - 1)) = 0 := by omega
                have h0 := (Finset.sum_eq_zero_iff.mp hrest0) w (Finset.mem_erase.mpr ⟨hne, hw⟩)
                have hpos := hcnt_pos w hw
                omega
              have hno_escape : ∀ u ∈ D.ancStop p out, u ≠ p → u ∉ D.anc p := by
                by_contra hex
                push Not at hex
                let Bad := (D.ancStop p out ∩ D.anc p).erase p
                have hBad_ne : Bad.Nonempty := by
                  rcases hex with ⟨u, hu1, hne, hu2⟩
                  exact ⟨u, Finset.mem_erase.mpr ⟨hne, Finset.mem_inter.mpr ⟨hu1, hu2⟩⟩⟩
                let u := Bad.max' hBad_ne
                have hu_mem := Finset.max'_mem Bad hBad_ne
                have hu_nep : u ≠ p := Finset.ne_of_mem_erase hu_mem
                have hu_stop : u ∈ D.ancStop p out := (Finset.mem_inter.mp (Finset.mem_of_mem_erase hu_mem)).1
                have hu_ancp : u ∈ D.anc p := (Finset.mem_inter.mp (Finset.mem_of_mem_erase hu_mem)).2
                have hu_neout : u ≠ out := by
                  have h1 := D.anc_le p u hu_ancp
                  have h2 := D.anc_le out p (Finset.mem_of_mem_erase hpW)
                  have h3 := Finset.ne_of_mem_erase hpW
                  omega
                obtain ⟨j1, hj1_stop, hj1_nep, hj1_use⟩ := D.ancStop_pred p out u hu_stop hu_neout
                obtain ⟨j2, hj2_ancp, hj2_use⟩ := D.anc_pred p u hu_ancp hu_nep
                have hj1_act : j1 ∈ Act := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, D.ancStop_sub_anc p out hout hj1_stop⟩
                have hj2_act : j2 ∈ Act := Finset.mem_filter.mpr
                  ⟨Finset.mem_univ _, D.anc_sub out p (Finset.mem_of_mem_erase hpW) hj2_ancp⟩
                have hj_ne : j1 ≠ j2 := by
                  intro heq; subst heq
                  have hmem_bad : 8 + j1.val ∈ Bad :=
                    Finset.mem_erase.mpr ⟨hj1_nep, Finset.mem_inter.mpr ⟨hj1_stop, hj2_ancp⟩⟩
                  have hle := Finset.le_max' Bad _ hmem_bad
                  have hlt : u < 8 + j1.val := by
                    rcases hj1_use with ha | ⟨hop1, hb⟩
                    · rw [← ha]; exact D.ha j1
                    · rw [← hb]; exact D.hb j1 hop1
                  omega
                have huW : u ∈ W := Finset.mem_erase.mpr ⟨hu_neout, D.ancStop_sub_anc p out hout hu_stop⟩
                have h2 := hcnt_two_of_two_uses u huW j1 j2 hj1_act hj2_act hj_ne hj1_use hj2_use
                have h1 := hcnt_other u huW hu_nep
                omega
              let S : Finset (Fin 8) := Finset.univ.filter fun i => i.val ∈ D.anc p
              have hp_lt : p < 8 + m := hReach_sub p (Finset.mem_of_mem_erase hpW)
              have hS_ne : S.Nonempty := by
                obtain ⟨i, hi⟩ := D.anc_has_input p hp_lt
                exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
              have hS_card_ge1 : 1 ≤ S.card := Finset.card_pos.mpr hS_ne
              have hS_card_le8 : S.card ≤ 8 := Finset.card_le_univ S |>.trans (by simp)
              have hG_dep : ∀ y z, (∀ i ∈ S, y i = z i) → D.val y p = D.val z p := fun y z h =>
                D.val_eq_of_agree_anc y z p hp_lt fun i hi => h i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
              have hG_mono : ∀ y z, (∀ i ∈ S, y i = true → z i = true) → D.val y p = true → D.val z p = true := by
                intro y z hle hy
                let z' : Fin 8 → Bool := fun i => if i ∈ S then z i else y i
                have hz' : D.val z' p = D.val z p := hG_dep z' z fun i hi => by simp [z', hi]
                rw [← hz']
                refine hmono_all p (Finset.mem_of_mem_erase hpW) y z' (fun i hi => ?_) hy
                by_cases hiS : i ∈ S
                · simp [z', hiS, hle i hiS hi]
                · simp [z', hiS, hi]
              have hf_dep : ∀ y z, D.val y p = D.val z p → (∀ i ∉ S, y i = z i) → f8 y = f8 z := by
                intro y z hp_eq hagr
                rw [← hf y, ← hf z]
                refine D.val_eq_of_agree_ancStop p y z hp_eq out hout fun i hi hne => ?_
                have hniS : i ∉ S := fun hiS => hno_escape i.val hi hne (Finset.mem_filter.mp hiS).2
                exact hagr i hniS
              by_cases hS8 : S.card = 8
              · have hSuniv : S = Finset.univ := Finset.eq_univ_of_card S (by simpa using hS8)
                have hfp_dep : ∀ y z, D.val y p = D.val z p → f8 y = f8 z := fun y z hp_eq =>
                  hf_dep y z hp_eq fun i hi => absurd (hSuniv ▸ Finset.mem_univ i) hi
                have hfp_eq : ∀ y, D.val y p = f8 y := by
                  have h0 : f8 (fun _ => false) = false := by decide
                  have h1 : f8 (fun _ => true) = true := by decide
                  have hp0 : D.val (fun _ => false) p = false := by
                    cases h : D.val (fun _ => false) p
                    · rfl
                    · exfalso
                      have hp1' : D.val (fun _ => true) p = true :=
                        hmono_all p (Finset.mem_of_mem_erase hpW) _ _ (fun _ _ => rfl) h
                      have := hfp_dep _ _ (h.trans hp1'.symm)
                      rw [h0, h1] at this; cases this
                  have hp1' : D.val (fun _ => true) p = true := by
                    cases h : D.val (fun _ => true) p
                    · exfalso
                      have := hfp_dep _ _ (hp0.trans h.symm)
                      rw [h0, h1] at this; cases this
                    · rfl
                  intro y
                  cases hy : D.val y p
                  · rw [hfp_dep y (fun _ => false) (hy.trans hp0.symm), h0]
                  · rw [hfp_dep y (fun _ => true) (hy.trans hp1'.symm), h1]
                have hp_lt_out : p < out := by
                  have := D.anc_le out p (Finset.mem_of_mem_erase hpW)
                  have := Finset.ne_of_mem_erase hpW
                  omega
                by_cases hp8 : p < 8
                · let i0 : Fin 8 := ⟨p, hp8⟩
                  let i1 : Fin 8 := ⟨(p + 1) % 8, Nat.mod_lt _ (by decide)⟩
                  have hne : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
                  obtain ⟨y, hy⟩ := f8_essential i1
                  apply hy
                  rw [← hfp_eq y, ← hfp_eq (Function.update y i1 (!y i1)), DAG.val_input D y i0, DAG.val_input D _ i0]
                  simp [Function.update_of_ne hne.symm]
                · let m' := p - 7
                  have hm' : m' < m := by omega
                  refine ih m' hm' (by omega) (D.truncate m' (le_of_lt hm')) p (by omega) fun y => ?_
                  rw [D.val_truncate m' (le_of_lt hm') y p (by omega), hfp_eq y]
              · by_cases hS2 : 2 ≤ S.card
                · exact f8_no_module S hS2 (by omega) (fun y => D.val y p) hG_dep hG_mono hf_dep
                · have hS1 : S.card = 1 := by omega
                  obtain ⟨s, hs_eq⟩ := Finset.card_eq_one.mp hS1
                  have hps_eq : ∀ y, D.val y p = y s := by
                    have hs_in : s ∈ S := hs_eq ▸ Finset.mem_singleton_self s
                    have hdep_s : ∀ y z, y s = z s → D.val y p = D.val z p := fun y z hys =>
                      hG_dep y z fun i hi => by
                        have : i = s := Finset.mem_singleton.mp (hs_eq ▸ hi)
                        exact this ▸ hys
                    have h0 : D.val (fun _ => false) p = false := by
                      cases h : D.val (fun _ => false) p
                      · rfl
                      · exfalso
                        have hall : ∀ y, D.val y p = true := fun y =>
                          hmono_all p (Finset.mem_of_mem_erase hpW) _ y (fun _ h0 => by cases h0) h
                        obtain ⟨y, hy⟩ := f8_essential s
                        apply hy
                        refine hf_dep y (Function.update y s (!y s)) (by rw [hall, hall]) fun i hi => ?_
                        have his : i ≠ s := fun heq => hi (heq ▸ hs_in)
                        simp [Function.update_of_ne his]
                    have h1 : D.val (fun _ => true) p = true := by
                      cases h : D.val (fun _ => true) p
                      · exfalso
                        have hall : ∀ y, D.val y p = false := fun y => by
                          cases hy : D.val y p
                          · rfl
                          · have := hmono_all p (Finset.mem_of_mem_erase hpW) y _ (fun _ _ => rfl) hy
                            rw [h] at this; cases this
                        obtain ⟨y, hy⟩ := f8_essential s
                        apply hy
                        refine hf_dep y (Function.update y s (!y s)) (by rw [hall, hall]) fun i hi => ?_
                        have his : i ≠ s := fun heq => hi (heq ▸ hs_in)
                        simp [Function.update_of_ne his]
                      · rfl
                    intro y
                    cases hys : y s
                    · rw [hdep_s y (fun _ => false) hys, h0]
                    · rw [hdep_s y (fun _ => true) hys, h1]
                  have hdisj_stop : Disjoint ((D.ancStop p c1).erase p) ((D.ancStop p c2).erase p) := by
                    rw [Finset.disjoint_iff_inter_eq_empty]
                    by_contra hne
                    let IntS := (D.ancStop p c1).erase p ∩ (D.ancStop p c2).erase p
                    have hInt_ne : IntS.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
                    let w := IntS.max' hInt_ne
                    have hw_mem := Finset.max'_mem IntS hInt_ne
                    have hw1_e := (Finset.mem_inter.mp hw_mem).1
                    have hw2_e := (Finset.mem_inter.mp hw_mem).2
                    have hw_nep : w ≠ p := Finset.ne_of_mem_erase hw1_e
                    have hw1 : w ∈ D.ancStop p c1 := Finset.mem_of_mem_erase hw1_e
                    have hw2 : w ∈ D.ancStop p c2 := Finset.mem_of_mem_erase hw2_e
                    have hwW : w ∈ W := by
                      refine Finset.mem_erase.mpr ⟨?_, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) (D.ancStop_sub_anc p c1 hc1_lt hw1)⟩
                      have := D.ancStop_le p c1 w hw1; have := D.ha jout; omega
                    have h2 : 2 ≤ cnt w := by
                      by_cases hwc1 : w = c1
                      · obtain ⟨k2, hk2_s, _, hk2_u⟩ := D.ancStop_pred p c2 w hw2 (hwc1.symm ▸ hcne)
                        have hk2_act : k2 ∈ Act := Finset.mem_filter.mpr
                          ⟨Finset.mem_univ _, D.anc_sub out c2 (Finset.mem_of_mem_erase hc2W) (D.ancStop_sub_anc p c2 hc2_lt hk2_s)⟩
                        have hk2_ne : k2 ≠ jout := by
                          intro h; subst h; have := D.ancStop_le p c2 (8 + jout.val) hk2_s; have := D.hb jout hop_out_ne; omega
                        exact hcnt_two_of_two_uses w hwW jout k2 hjout_act hk2_act hk2_ne.symm (Or.inl hwc1.symm) hk2_u
                      · by_cases hwc2 : w = c2
                        · obtain ⟨k1, hk1_s, _, hk1_u⟩ := D.ancStop_pred p c1 w hw1 hwc1
                          have hk1_act : k1 ∈ Act := Finset.mem_filter.mpr
                            ⟨Finset.mem_univ _, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) (D.ancStop_sub_anc p c1 hc1_lt hk1_s)⟩
                          have hk1_ne : k1 ≠ jout := by
                            intro h; subst h; have := D.ancStop_le p c1 (8 + jout.val) hk1_s; have := D.ha jout; omega
                          exact hcnt_two_of_two_uses w hwW jout k1 hjout_act hk1_act hk1_ne.symm (Or.inr ⟨hop_out_ne, hwc2.symm⟩) hk1_u
                        · obtain ⟨k1, hk1_s, hk1_nep, hk1_u⟩ := D.ancStop_pred p c1 w hw1 hwc1
                          obtain ⟨k2, hk2_s, _, hk2_u⟩ := D.ancStop_pred p c2 w hw2 hwc2
                          have hk1_act : k1 ∈ Act := Finset.mem_filter.mpr
                            ⟨Finset.mem_univ _, D.anc_sub out c1 (Finset.mem_of_mem_erase hc1W) (D.ancStop_sub_anc p c1 hc1_lt hk1_s)⟩
                          have hk2_act : k2 ∈ Act := Finset.mem_filter.mpr
                            ⟨Finset.mem_univ _, D.anc_sub out c2 (Finset.mem_of_mem_erase hc2W) (D.ancStop_sub_anc p c2 hc2_lt hk2_s)⟩
                          have hk_ne : k1 ≠ k2 := by
                            intro h; subst h
                            have hmem : 8 + k1.val ∈ IntS := Finset.mem_inter.mpr
                              ⟨Finset.mem_erase.mpr ⟨hk1_nep, hk1_s⟩, Finset.mem_erase.mpr ⟨hk1_nep, hk2_s⟩⟩
                            have hle := Finset.le_max' IntS _ hmem
                            have hlt : w < 8 + k1.val := by
                              rcases hk1_u with ha | ⟨hop1, hb⟩
                              · rw [← ha]; exact D.ha k1
                              · rw [← hb]; exact D.hb k1 hop1
                            omega
                          exact hcnt_two_of_two_uses w hwW k1 k2 hk1_act hk2_act hk_ne hk1_u hk2_u
                    have h1 := hcnt_other w hwW hw_nep
                    omega
                  let L : Finset (Fin 8) := Finset.univ.filter fun i => i.val ∈ (D.ancStop p c1).erase p
                  have hsL : s ∉ L := by
                    intro hs
                    have hs_mem := (Finset.mem_filter.mp hs).2
                    have hs_nep : s.val ≠ p := Finset.ne_of_mem_erase hs_mem
                    have hs_stop_out : s.val ∈ D.ancStop p out := by
                      rw [hjout_val, D.ancStop_gate_bin p jout (hjout_val ▸ (Finset.ne_of_mem_erase hpW).symm) hop_out_ne]
                      exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_of_mem_erase hs_mem))
                    have hs_ancp : s.val ∈ D.anc p := by
                      have : s ∈ S := hs_eq ▸ Finset.mem_singleton_self s
                      exact (Finset.mem_filter.mp this).2
                    exact hno_escape s.val hs_stop_out hs_nep hs_ancp
                  have hdepA : ∀ y z, y s = z s → (∀ i ∈ L, y i = z i) → D.val y c1 = D.val z c1 := by
                    intro y z hys hL
                    refine D.val_eq_of_agree_ancStop p y z (by rw [hps_eq, hps_eq, hys]) c1 hc1_lt fun i hi hne => ?_
                    exact hL i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.mem_erase.mpr ⟨hne, hi⟩⟩)
                  have hdepB : ∀ y z, y s = z s → (∀ i, i ≠ s → i ∉ L → y i = z i) → D.val y c2 = D.val z c2 := by
                    intro y z hys hR
                    refine D.val_eq_of_agree_ancStop p y z (by rw [hps_eq, hps_eq, hys]) c2 hc2_lt fun i hi hne => ?_
                    have hi_notL : i ∉ L := fun hiL =>
                      Finset.disjoint_left.mp hdisj_stop (Finset.mem_filter.mp hiL).2 (Finset.mem_erase.mpr ⟨hne, hi⟩)
                    have his : i ≠ s := by
                      intro heq; subst heq
                      have hs_stop_out : i.val ∈ D.ancStop p out := by
                        rw [hjout_val, D.ancStop_gate_bin p jout (hjout_val ▸ (Finset.ne_of_mem_erase hpW).symm) hop_out_ne]
                        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hi)
                      have hs_ancp : i.val ∈ D.anc p := by
                        have : i ∈ S := hs_eq ▸ Finset.mem_singleton_self i
                        exact (Finset.mem_filter.mp this).2
                      exact hno_escape i.val hs_stop_out hne hs_ancp
                    exact hR i his hi_notL
                  have hmonoA : ∀ y z, (∀ i, y i = true → z i = true) → D.val y c1 = true → D.val z c1 = true :=
                    hmono_all c1 (Finset.mem_of_mem_erase hc1W)
                  have hmonoB : ∀ y z, (∀ i, y i = true → z i = true) → D.val y c2 = true → D.val z c2 = true :=
                    hmono_all c2 (Finset.mem_of_mem_erase hc2W)
                  have hchild_lt : ∀ c, c < out → (∀ y, D.val y c = f8 y) → False := by
                    intro c hc hfc
                    by_cases hc8 : c < 8
                    · let i0 : Fin 8 := ⟨c, hc8⟩
                      let i1 : Fin 8 := ⟨(c + 1) % 8, Nat.mod_lt _ (by decide)⟩
                      have hne : i1 ≠ i0 := by intro h; have := congrArg Fin.val h; dsimp [i0, i1] at this; omega
                      obtain ⟨y, hy⟩ := f8_essential i1
                      apply hy
                      rw [← hfc y, ← hfc (Function.update y i1 (!y i1)), DAG.val_input D y i0, DAG.val_input D _ i0]
                      simp [Function.update_of_ne hne.symm]
                    · let m' := c - 7
                      have hm' : m' < m := by omega
                      refine ih m' hm' (by omega) (D.truncate m' (le_of_lt hm')) c (by omega) fun y => ?_
                      rw [D.val_truncate m' (le_of_lt hm') y c (by omega), hfc y]
                  have hsingle_or_and : ∀ (cA cB : ℕ), cA < out → cB < out →
                      (∀ y z, y s = z s → D.val y cA = D.val z cA) →
                      (∀ y z, (∀ i, y i = true → z i = true) → D.val y cA = true → D.val z cA = true) →
                      (∀ y z, (∀ i, y i = true → z i = true) → D.val y cB = true → D.val z cB = true) →
                      ((∀ y, f8 y = (D.val y cA && D.val y cB)) ∨ (∀ y, f8 y = (D.val y cA || D.val y cB))) → False := by
                    intro cA cB hcA hcB hdep_sA hmA hmB hform
                    have h0f : f8 (fun _ => false) = false := by decide
                    have h1f : f8 (fun _ => true) = true := by decide
                    cases hA0 : D.val (fun _ => false) cA
                    · cases hA1 : D.val (fun _ => true) cA
                      · have hconstA : ∀ y, D.val y cA = false := fun y => by
                          cases h : y s
                          · rw [hdep_sA y (fun _ => false) h, hA0]
                          · rw [hdep_sA y (fun _ => true) h, hA1]
                        rcases hform with hf' | hf'
                        · have := hf' (fun _ => true); rw [h1f, hconstA] at this; cases this
                        · exact hchild_lt cB hcB fun y => by have := hf' y; rw [hconstA] at this; simpa using this.symm
                      · have hAs : ∀ y, D.val y cA = y s := fun y => by
                          cases h : y s
                          · rw [hdep_sA y (fun _ => false) h, hA0]
                          · rw [hdep_sA y (fun _ => true) h, hA1]
                        rcases hform with hf' | hf'
                        · refine f8_no_disjoint_and {s} (Finset.singleton_nonempty s)
                            (by intro hu; have := congrArg Finset.card hu; simp at this)
                            (fun y => y s) (fun y => D.val (Function.update y s true) cB)
                            (fun y z h => h s (Finset.mem_singleton_self s))
                            (fun y z h => by
                              congr 1; funext i
                              by_cases his : i = s
                              · subst his; simp
                              · simp [Function.update_of_ne his, h i (by simp [his])])
                            fun y => ?_
                          rw [hf' y, hAs y]
                          cases hys : y s
                          · simp
                          · have hupd : Function.update y s true = y := by
                              funext i; by_cases hi : i = s
                              · subst hi; simp [hys]
                              · simp [Function.update_of_ne hi]
                            simp [hupd]
                        · refine f8_no_disjoint_or {s} (Finset.singleton_nonempty s)
                            (by intro hu; have := congrArg Finset.card hu; simp at this)
                            (fun y => y s) (fun y => D.val (Function.update y s false) cB)
                            (fun y z h => h s (Finset.mem_singleton_self s))
                            (fun y z h => by
                              congr 1; funext i
                              by_cases his : i = s
                              · subst his; simp
                              · simp [Function.update_of_ne his, h i (by simp [his])])
                            fun y => ?_
                          rw [hf' y, hAs y]
                          cases hys : y s
                          · have hupd : Function.update y s false = y := by
                              funext i; by_cases hi : i = s
                              · subst hi; simp [hys]
                              · simp [Function.update_of_ne hi]
                            simp [hupd]
                          · simp
                    · have hconstA : ∀ y, D.val y cA = true := fun y =>
                        hmA (fun _ => false) y (fun _ h => by cases h) hA0
                      rcases hform with hf' | hf'
                      · exact hchild_lt cB hcB fun y => by have := hf' y; rw [hconstA] at this; simpa using this.symm
                      · have := hf' (fun _ => false); rw [h0f, hconstA] at this; cases this
                  have hform_out : (∀ y, f8 y = (D.val y c1 && D.val y c2)) ∨
                      (∀ y, f8 y = (D.val y c1 || D.val y c2)) := by
                    cases hopo : (D.nodes jout).op
                    · exact Or.inl fun y => by rw [← hf y, hjout_val, DAG.val_gate_and D y jout hopo]
                    · exact Or.inr fun y => by rw [← hf y, hjout_val, DAG.val_gate_or D y jout hopo]
                    · exact absurd hopo hop_out_ne
                  by_cases hLne : L.Nonempty
                  · by_cases hRne : (Finset.univ.erase s \ L).Nonempty
                    · rcases hform_out with hf_and | hf_or
                      · exact f8_no_sv_and s L hsL hLne hRne (fun y => D.val y c1) (fun y => D.val y c2)
                          hdepA hdepB hmonoA hmonoB hf_and
                      · exact f8_no_sv_or s L hsL hLne hRne (fun y => D.val y c1) (fun y => D.val y c2)
                          hdepA hdepB hmonoA hmonoB hf_or
                    · rw [Finset.not_nonempty_iff_eq_empty] at hRne
                      have hdep_sB : ∀ y z, y s = z s → D.val y c2 = D.val z c2 := fun y z hys =>
                        hdepB y z hys fun i his hiL => by
                          exfalso
                          have : i ∈ Finset.univ.erase s \ L :=
                            Finset.mem_sdiff.mpr ⟨Finset.mem_erase.mpr ⟨his, Finset.mem_univ _⟩, hiL⟩
                          rw [hRne] at this; simp at this
                      exact hsingle_or_and c2 c1 (by have := D.hb jout hop_out_ne; omega)
                        (by have := D.ha jout; omega) hdep_sB hmonoB hmonoA (by
                          rcases hform_out with h | h
                          · exact Or.inl fun y => by rw [h y, Bool.and_comm]
                          · exact Or.inr fun y => by rw [h y, Bool.or_comm])
                  · rw [Finset.not_nonempty_iff_eq_empty] at hLne
                    have hdep_sA : ∀ y z, y s = z s → D.val y c1 = D.val z c1 := fun y z hys =>
                      hdepA y z hys fun i hi => by rw [hLne] at hi; simp at hi
                    exact hsingle_or_and c1 c2 (by have := D.ha jout; omega)
                      (by have := D.hb jout hop_out_ne; omega) hdep_sA hmonoA hmonoB hform_out

theorem wires_foldl_prefix (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (i : ℕ) (hi : i < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w).getD i false =
    w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).length := by
      rw [List.length_append]; omega
    rw [ih _ hlt]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wires_getD_input (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool)
    (i : ℕ) (hi : i < x.length) :
    (C.wires x).getD i false = x.getD i false :=
  wires_foldl_prefix C.gates x i hi

theorem wires_foldl_gate (gs : List PEqualNP.CircuitLowerBounds.Gate) (w : List Bool)
    (j : ℕ) (hj : j < gs.length)
    (hvalid : ∀ k ∈ (gs.get ⟨j, hj⟩).inputs, k < w.length + j) :
    let res := gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]) w
    res.getD (w.length + j) false =
    (gs.get ⟨j, hj⟩).op.eval ((gs.get ⟨j, hj⟩).inputs.map fun k => res.getD k false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [List.foldl_cons, Nat.add_zero, List.get_eq_getElem, List.getElem_cons_zero]
      let w1 := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
      have hlen : w.length < w1.length := by simp [w1]
      rw [wires_foldl_prefix gs w1 w.length hlen]
      have hval_last : w1.getD w.length false = g.op.eval (g.inputs.map fun k => w.getD k false) := by
        simp [w1, List.getD_eq_getElem?_getD]
      rw [hval_last]
      congr 1
      refine List.map_congr_left fun k hk => ?_
      have hk_lt : k < w.length := by simpa using hvalid k hk
      rw [wires_foldl_prefix gs w1 k (by simp [w1]; omega)]
      simp [w1, List.getD_eq_getElem?_getD, List.getElem?_append_left hk_lt]
    | succ j =>
      simp only [List.foldl_cons]
      let w1 := w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]
      have hw1_len : w1.length = w.length + 1 := by simp [w1]
      have hj' : j < gs.length := Nat.lt_of_succ_lt_succ hj
      have hvalid' : ∀ k ∈ (gs.get ⟨j, hj'⟩).inputs, k < w1.length + j := by
        intro k hk
        have := hvalid k (by simpa using hk)
        omega
      have hrec := ih w1 j hj' hvalid'
      simpa [w1, hw1_len, show w.length + 1 + j = w.length + (j + 1) by omega] using hrec

theorem wires_getD_gate (C : PEqualNP.CircuitLowerBounds.Circuit) (x : List Bool)
    (j : Fin C.gates.length) (hvalid : ∀ k ∈ (C.gates.get j).inputs, k < x.length + j.val) :
    (C.wires x).getD (x.length + j.val) false =
    (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k => (C.wires x).getD k false) :=
  wires_foldl_gate C.gates x j.val j.isLt hvalid

noncomputable def resolveWire (s : ℕ) (B : Finset (Fin s)) (idxOf : Fin s → ℕ)
    (byp : ∀ j : Fin s, j ∈ B → ℕ) (hbyp_lt : ∀ j (hj : j ∈ B), byp j hj < 9 + j.val) : ℕ → ℕ
  | w =>
    if h9 : w < 9 then w - 1
    else if hs' : w - 9 < s then
      let j : Fin s := ⟨w - 9, hs'⟩
      if hjB : j ∈ B then
        have hlt : byp j hjB < w := by
          have hw_eq : 9 + j.val = w := by dsimp [j]; omega
          exact hw_eq ▸ hbyp_lt j hjB
        resolveWire s B idxOf byp hbyp_lt (byp j hjB)
      else 8 + idxOf j
    else 0
termination_by w => w

theorem main_refute :
    ¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
      (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = pm3 x) ∧
      C.output + 1 = 9 + C.size ∧
      (∀ j : Fin C.gates.length,
        ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
            ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
        (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
            (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
            ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
      (∀ j : Fin C.gates.length,
        (∃ x y : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
        ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
          (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
      (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
        ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
      C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
      C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩) := by
  classical
  rintro ⟨C, _hfit, hsize, heval, hout, hform, _hnonconst, hused, hhead, htail⟩
  let s := C.gates.length
  have hs_le12 : s ≤ 12 := hsize
  have hs_ge2 : 2 ≤ s := by
    cases hg : C.gates with
    | nil => simp [hg] at hhead
    | cons g0 gs =>
      cases gs with
      | nil => simp [hg] at htail
      | cons g1 rest => simp [s, hg]
  have hg0 : C.gates.get ⟨0, by omega⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ := by
    have h0 : C.gates[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ := by
      simpa [List.head?_eq_getElem?] using hhead
    rw [List.getElem?_eq_getElem (by omega)] at h0
    exact Option.some.inj h0
  have hg1 : C.gates.get ⟨1, by omega⟩ = ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩ := by
    have h1 : C.gates[1]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩ := by
      have ht : C.gates.tail[0]? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩ := by
        simpa [List.head?_eq_getElem?] using htail
      simpa [List.getElem?_tail] using ht
    rw [List.getElem?_eq_getElem (by omega)] at h1
    exact Option.some.inj h1
  have hin_lt : ∀ j : Fin C.gates.length, ∀ k ∈ (C.gates.get j).inputs, k < 9 + j.val := by
    intro j k hk
    rcases hform j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
    · rw [hin] at hk; simp at hk; omega
    · rw [hin] at hk; simp at hk; rcases hk with rfl | rfl <;> omega
  have hwire_in : ∀ (x : Fin 9 → Bool) (i : Fin 9),
      (C.wires (List.ofFn x)).getD i.val false = x i := by
    intro x i
    rw [wires_getD_input C (List.ofFn x) i.val (by simp),
      List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have hwire_gate : ∀ (x : Fin 9 → Bool) (j : Fin C.gates.length),
      (C.wires (List.ofFn x)).getD (9 + j.val) false =
      (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k => (C.wires (List.ofFn x)).getD k false) := by
    intro x j
    have hlen : (List.ofFn x).length = 9 := by simp
    have h := wires_getD_gate C (List.ofFn x) j (by simpa [hlen] using hin_lt j)
    simpa [hlen] using h
  let ext0 : (Fin 8 → Bool) → (Fin 9 → Bool) := fun y => Fin.cons false y
  have hpm3_ext0 : ∀ y : Fin 8 → Bool, pm3 (ext0 y) = f8 y := by
    intro y
    have h0 : ext0 y 0 = false := rfl
    have h1 : ext0 y 1 = y 0 := rfl
    have h2 : ext0 y 2 = y 1 := rfl
    have h3 : ext0 y 3 = y 2 := rfl
    have h4 : ext0 y 4 = y 3 := rfl
    have h5 : ext0 y 5 = y 4 := rfl
    have h6 : ext0 y 6 = y 5 := rfl
    have h7 : ext0 y 7 = y 6 := rfl
    have h8 : ext0 y 8 = y 7 := rfl
    simp [pm3, f8, h0, h1, h2, h3, h4, h5, h6, h7, h8]
  let wval (w : ℕ) (y : Fin 8 → Bool) : Bool := (C.wires (List.ofFn (ext0 y))).getD w false
  have hwval_gate : ∀ (j : Fin C.gates.length) (y : Fin 8 → Bool),
      wval (9 + j.val) y = (C.gates.get j).op.eval ((C.gates.get j).inputs.map fun k => wval k y) :=
    fun j y => hwire_gate (ext0 y) j
  have hwval_0 : ∀ y, wval 0 y = false := fun y => by
    have := hwire_in (ext0 y) 0; simpa [wval, ext0] using this
  have hwval_in : ∀ (i : Fin 8) y, wval (1 + i.val) y = y i := fun i y => by
    have := hwire_in (ext0 y) i.succ
    simpa [wval, ext0, Nat.add_comm] using this
  have hwval_g0 : ∀ y, wval 9 y = false := fun y => by
    have h := hwval_gate ⟨0, by omega⟩ y
    rw [hg0] at h
    simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hwval_0 y] using h
  have hwval_g1 : ∀ y, wval 10 y = false := fun y => by
    have h := hwval_gate ⟨1, by omega⟩ y
    rw [hg1] at h
    simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hwval_g0 y] using h
  have hout_eq : C.output = 9 + (s - 1) := by
    have hout' : C.output + 1 = 9 + s := hout
    omega
  have hwval_out : ∀ y, wval (9 + (s - 1)) y = f8 y := fun y => by
    have h := heval (ext0 y)
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval, hout_eq, hpm3_ext0] at h
    exact h
  have hs_ge3 : 3 ≤ s := by
    by_contra hlt
    have hs2 : s = 2 := by omega
    have h1 := hwval_out ![true, false, true, false, false, false, false, true]
    rw [show 9 + (s - 1) = 10 by omega, hwval_g1] at h1
    simp [f8] at h1
  let K : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    ∃ c : Bool, ∀ y : Fin 8 → Bool, wval (9 + j.val) y = c
  let isConstW (w : ℕ) : Prop := w = 0 ∨ ∃ k ∈ K, w = 9 + k.val
  have hconstW_spec : ∀ w, isConstW w → ∃ c : Bool, ∀ y, wval w y = c := by
    rintro w (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨false, hwval_0⟩
    · exact (Finset.mem_filter.mp hk).2
  let B : Finset (Fin C.gates.length) := Finset.univ.filter fun j =>
    j ∉ K ∧ ∃ w ∈ (C.gates.get j).inputs, isConstW w
  have hj0_K : (⟨0, by omega⟩ : Fin C.gates.length) ∈ K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨false, hwval_g0⟩⟩
  have hj1_K : (⟨1, by omega⟩ : Fin C.gates.length) ∈ K :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨false, hwval_g1⟩⟩
  have hjlast_notK : (⟨s - 1, by omega⟩ : Fin C.gates.length) ∉ K := by
    intro h
    obtain ⟨c, hc⟩ := (Finset.mem_filter.mp h).2
    have h0 := hc (fun _ => false)
    have h1 := hc (fun _ => true)
    rw [hwval_out] at h0 h1
    have hf0 : f8 (fun _ => false) = false := by decide
    have hf1 : f8 (fun _ => true) = true := by decide
    rw [hf0] at h0; rw [hf1] at h1; rw [← h0] at h1; cases h1
  have hK_ge2 : 2 ≤ K.card := by
    have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)) ⊆ K := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hne : (⟨0, by omega⟩ : Fin C.gates.length) ≠ ⟨1, by omega⟩ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
    calc 2 = ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)).card := (Finset.card_pair hne).symm
      _ ≤ K.card := Finset.card_le_card hsub
  have hB_ge1 : 1 ≤ B.card := by
    have hKne : K.Nonempty := ⟨⟨0, by omega⟩, hj0_K⟩
    let mK := K.max' hKne
    have hmK_mem : mK ∈ K := Finset.max'_mem K hKne
    have hmK_lt : mK.val + 1 < C.gates.length := by
      by_contra hge
      have heq : mK = ⟨s - 1, by omega⟩ := Fin.ext (by dsimp; omega)
      exact hjlast_notK (heq ▸ hmK_mem)
    obtain ⟨k, hkm, hk_in⟩ := hused mK hmK_lt
    have hk_notK : k ∉ K := by
      intro hkK
      have hle : k ≤ mK := Finset.le_max' K k hkK
      exact absurd hkm (not_lt.mpr hle)
    have hk_B : k ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk_notK, 9 + mK.val, hk_in, Or.inr ⟨mK, hmK_mem, rfl⟩⟩
    exact Finset.card_pos.mpr ⟨k, hk_B⟩
  have hKB_ge4 : 4 ≤ K.card + B.card := by
    by_contra hlt
    have hK2 : K.card = 2 := by omega
    have hB1 : B.card = 1 := by omega
    have hK_eq : K = {⟨0, by omega⟩, ⟨1, by omega⟩} := by
      have hsub : ({⟨0, by omega⟩, ⟨1, by omega⟩} : Finset (Fin C.gates.length)) ⊆ K := by
        intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl <;> assumption
      have hne : (⟨0, by omega⟩ : Fin C.gates.length) ≠ ⟨1, by omega⟩ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
      exact (Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_pair hne]; omega)).symm
    obtain ⟨b0, hB_eq⟩ := Finset.card_eq_one.mp hB1
    have hb0_mem : b0 ∈ B := hB_eq ▸ Finset.mem_singleton_self b0
    have hb0_notK : b0 ∉ K := (Finset.mem_filter.mp hb0_mem).2.1
    obtain ⟨k1, hk1_gt, hk1_in⟩ := hused ⟨1, by omega⟩ (by dsimp; omega)
    have hk1_notK : k1 ∉ K := by
      rw [hK_eq]; intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h <;> (have := congrArg Fin.val h; dsimp at this hk1_gt; omega)
    have hk1_B : k1 ∈ B := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, hk1_notK, 10, hk1_in, Or.inr ⟨⟨1, by omega⟩, hj1_K, rfl⟩⟩
    have hk1_eq : k1 = b0 := Finset.mem_singleton.mp (hB_eq ▸ hk1_B)
    have h10_in_b0 : 10 ∈ (C.gates.get b0).inputs := hk1_eq ▸ hk1_in
    have hno_0_ge2 : ∀ j : Fin C.gates.length, 2 ≤ j.val → 0 ∉ (C.gates.get j).inputs := by
      intro j hj2 h0in
      have hj_notK : j ∉ K := by
        rw [hK_eq]; intro h; simp only [Finset.mem_insert, Finset.mem_singleton] at h
        rcases h with h | h <;> (have := congrArg Fin.val h; dsimp at this; omega)
      have hj_B : j ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_notK, 0, h0in, Or.inl rfl⟩
      have hjb0 : j = b0 := Finset.mem_singleton.mp (hB_eq ▸ hj_B)
      subst hjb0
      rcases hform j with ⟨hop, a, _, hin⟩ | ⟨hop, a, b, hab, _, hin⟩
      · rw [hin] at h0in h10_in_b0; simp at h0in h10_in_b0; omega
      · rw [hin] at h0in h10_in_b0; simp at h0in h10_in_b0
        have ha0 : a = 0 := by omega
        have hb10 : b = 10 := by omega
        subst ha0 hb10
        apply hb0_notK
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨false, fun y => ?_⟩⟩
        have hw := hwval_gate j y
        rw [hin] at hw
        rcases hop with hop | hop
        · rw [hop] at hw; simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hwval_0 y, hwval_g1 y] using hw
        · rw [hop] at hw; simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hwval_0 y, hwval_g1 y] using hw
    let x1 : Fin 9 → Bool := ![true, false, false, false, false, true, false, true, false]
    let x2 : Fin 9 → Bool := ![false, false, false, false, false, true, false, true, false]
    have hagree : ∀ w < 9 + s, w ≠ 0 →
        (C.wires (List.ofFn x1)).getD w false = (C.wires (List.ofFn x2)).getD w false := by
      intro w
      induction w using Nat.strongRecOn with
      | ind w ih =>
        intro hw hne0
        by_cases h9 : w < 9
        · rw [hwire_in x1 ⟨w, h9⟩, hwire_in x2 ⟨w, h9⟩]
          have hcases : w = 1 ∨ w = 2 ∨ w = 3 ∨ w = 4 ∨ w = 5 ∨ w = 6 ∨ w = 7 ∨ w = 8 := by omega
          rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
        · by_cases hw9 : w = 9
          · subst hw9
            have h1 := hwire_gate x1 ⟨0, by omega⟩
            have h2 := hwire_gate x2 ⟨0, by omega⟩
            rw [hg0] at h1 h2
            have hx41 : (C.wires (List.ofFn x1)).getD 4 false = false := by
              have h := hwire_in x1 4; simpa [x1] using h
            have hx42 : (C.wires (List.ofFn x2)).getD 4 false = false := by
              have h := hwire_in x2 4; simpa [x2] using h
            simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
              List.all_cons, List.all_nil, id_eq, hx41, hx42, Bool.and_false, Bool.and_true] at h1 h2
            exact h1.trans h2.symm
          · by_cases hw10 : w = 10
            · subst hw10
              have h1 := hwire_gate x1 ⟨1, by omega⟩
              have h2 := hwire_gate x2 ⟨1, by omega⟩
              rw [hg1] at h1 h2
              have hx81 : (C.wires (List.ofFn x1)).getD 8 false = false := by
                have h := hwire_in x1 8; simpa [x1] using h
              have hx82 : (C.wires (List.ofFn x2)).getD 8 false = false := by
                have h := hwire_in x2 8; simpa [x2] using h
              simp only [PEqualNP.CircuitLowerBounds.GateOp.eval, List.map_cons, List.map_nil,
                List.all_cons, List.all_nil, id_eq, hx81, hx82, Bool.false_and, Bool.and_true] at h1 h2
              exact h1.trans h2.symm
            · let j : Fin C.gates.length := ⟨w - 9, by omega⟩
              have hw_eq : w = 9 + j.val := by dsimp [j]; omega
              rw [hw_eq, hwire_gate x1 j, hwire_gate x2 j]
              congr 1
              refine List.map_congr_left fun k hk => ?_
              have hk_lt : k < 9 + j.val := hin_lt j k hk
              have hk_ne0 : k ≠ 0 := fun h0 => hno_0_ge2 j (by dsimp [j]; omega) (h0 ▸ hk)
              exact ih k (by omega) (by omega) hk_ne0
    have heq_eval := hagree C.output (by omega) (by omega)
    have h1 := heval x1
    have h2 := heval x2
    rw [PEqualNP.CircuitLowerBounds.Circuit.eval] at h1 h2
    rw [heq_eval, h2] at h1
    have hpm1 : pm3 x1 = true := by decide
    have hpm2 : pm3 x2 = false := by decide
    rw [hpm1, hpm2] at h1
    cases h1
  have hB_bypass : ∀ j ∈ B, ∃ w' < 9 + j.val, ¬ isConstW w' ∧ ∀ y, wval (9 + j.val) y = wval w' y := by
    intro j hjB
    obtain ⟨hj_notK, w1, hw1_in, hw1_const⟩ := (Finset.mem_filter.mp hjB).2
    rcases hform j with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
    · exfalso
      rw [hin] at hw1_in; simp at hw1_in
      obtain ⟨c, hc⟩ := hconstW_spec a (hw1_in ▸ hw1_const)
      apply hj_notK
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨!c, fun y => ?_⟩⟩
      have hw := hwval_gate j y
      rw [hin, hop] at hw
      simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hc y] using hw
    · rw [hin] at hw1_in; simp at hw1_in
      have hboth_const : ∀ u v, (C.gates.get j).inputs = [u, v] → isConstW u → isConstW v → False := by
        intro u v huv hu hv
        obtain ⟨cu, hcu⟩ := hconstW_spec u hu
        obtain ⟨cv, hcv⟩ := hconstW_spec v hv
        apply hj_notK
        rcases hop with hop | hop
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨cu && cv, fun y => ?_⟩⟩
          have hw := hwval_gate j y; rw [huv, hop] at hw
          simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hcu y, hcv y] using hw
        · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨cu || cv, fun y => ?_⟩⟩
          have hw := hwval_gate j y; rw [huv, hop] at hw
          simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hcu y, hcv y] using hw
      rcases hw1_in with hwa | hwb
      · have ha_const : isConstW a := hwa ▸ hw1_const
        have hnb : ¬ isConstW b := fun hbc => hboth_const a b hin ha_const hbc
        obtain ⟨ca, hca⟩ := hconstW_spec a ha_const
        refine ⟨b, hb, hnb, fun y => ?_⟩
        have hw := hwval_gate j y; rw [hin] at hw
        rcases hop with hop | hop
        · rw [hop] at hw
          cases ca
          · exfalso; apply hj_notK
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨false, fun z => ?_⟩⟩
            have hz := hwval_gate j z; rw [hin, hop] at hz
            simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hca z] using hz
          · simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hca y] using hw
        · rw [hop] at hw
          cases ca
          · simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hca y] using hw
          · exfalso; apply hj_notK
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨true, fun z => ?_⟩⟩
            have hz := hwval_gate j z; rw [hin, hop] at hz
            simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hca z] using hz
      · have hb_const : isConstW b := hwb ▸ hw1_const
        have hna : ¬ isConstW a := fun hac => hboth_const a b hin hac hb_const
        obtain ⟨cb, hcb⟩ := hconstW_spec b hb_const
        refine ⟨a, lt_trans hab hb, hna, fun y => ?_⟩
        have hw := hwval_gate j y; rw [hin] at hw
        rcases hop with hop | hop
        · rw [hop] at hw
          cases cb
          · exfalso; apply hj_notK
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨false, fun z => ?_⟩⟩
            have hz := hwval_gate j z; rw [hin, hop] at hz
            simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hcb z] using hz
          · simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hcb y] using hw
        · rw [hop] at hw
          cases cb
          · simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hcb y] using hw
          · exfalso; apply hj_notK
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨true, fun z => ?_⟩⟩
            have hz := hwval_gate j z; rw [hin, hop] at hz
            simpa [PEqualNP.CircuitLowerBounds.GateOp.eval, hcb z] using hz
  let R : Finset (Fin C.gates.length) := Finset.univ \ (K ∪ B)
  have hKB_disj : Disjoint K B := by
    rw [Finset.disjoint_left]
    intro j hjK hjB
    exact (Finset.mem_filter.mp hjB).2.1 hjK
  have hR_le8 : R.card ≤ 8 := by
    have h1 : (K ∪ B).card = K.card + B.card := Finset.card_union_of_disjoint hKB_disj
    have h2 : R.card = s - (K ∪ B).card := by
      simp [R, s, Finset.card_sdiff]
    omega
  let Rlist : List (Fin C.gates.length) := R.sort (· ≤ ·)
  have hRlist_len : Rlist.length = R.card := Finset.length_sort (· ≤ ·)
  have hRlist_sorted : Rlist.Pairwise (· ≤ ·) := R.pairwise_sort (· ≤ ·)
  have hRlist_mem : ∀ j, j ∈ Rlist ↔ j ∈ R := fun j => Finset.mem_sort (· ≤ ·)
  let m := Rlist.length
  have hm8 : m ≤ 8 := by omega
  let idxOf (j : Fin C.gates.length) : ℕ := Rlist.idxOf j
  have hidx_lt : ∀ j ∈ R, idxOf j < m := fun j hj => List.idxOf_lt_length_iff.mpr ((hRlist_mem j).mpr hj)
  have hidx_get : ∀ i : Fin m, idxOf (Rlist.get i) = i.val := fun i =>
    (R.sort_nodup (· ≤ ·)).idxOf_getElem i.val i.isLt
  have hidx_mono : ∀ j1 j2 : Fin C.gates.length, j1 ∈ R → j2 ∈ R → j1.val < j2.val → idxOf j1 < idxOf j2 := by
    intro j1 j2 hj1 hj2 hlt
    have hi1 : idxOf j1 < m := hidx_lt j1 hj1
    have hi2 : idxOf j2 < m := hidx_lt j2 hj2
    by_contra hge
    have hle : idxOf j2 ≤ idxOf j1 := by omega
    by_cases heq : idxOf j2 = idxOf j1
    · have := (List.idxOf_inj ((hRlist_mem j2).mpr hj2)).mp heq
      subst this; omega
    · have hrel := List.pairwise_iff_getElem.mp hRlist_sorted (idxOf j2) (idxOf j1) hi2 hi1 (by omega)
      simp only [idxOf, List.getElem_idxOf] at hrel
      exact absurd hlt (not_lt.mpr hrel)
  let byp (j : Fin C.gates.length) (hjB : j ∈ B) : ℕ := Classical.choose (hB_bypass j hjB)
  have hbyp_lt : ∀ j (hjB : j ∈ B), byp j hjB < 9 + j.val := fun j hjB =>
    (Classical.choose_spec (hB_bypass j hjB)).1
  let resolve (w : ℕ) : ℕ := resolveWire C.gates.length B idxOf byp hbyp_lt w
  have hres_lt : ∀ w < 9 + s, ¬ isConstW w →
      ∀ j : Fin C.gates.length, j ∈ R → w < 9 + j.val → resolve w < 8 + idxOf j := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hnc j hjR hwj
      dsimp only [resolve]; rw [resolveWire]
      by_cases h9 : w < 9
      · simp only [h9, ↓reduceDIte]; omega
      · have hs' : w - 9 < C.gates.length := by omega
        simp only [h9, hs', ↓reduceDIte]
        by_cases hjB : (⟨w - 9, hs'⟩ : Fin C.gates.length) ∈ B
        · simp only [hjB, ↓reduceDIte]
          have hspec := Classical.choose_spec (hB_bypass ⟨w - 9, hs'⟩ hjB)
          have hbw : byp ⟨w - 9, hs'⟩ hjB < w := by
            have := hbyp_lt ⟨w - 9, hs'⟩ hjB; dsimp at this; omega
          exact ih (byp ⟨w - 9, hs'⟩ hjB) hbw (by omega) hspec.2.1 j hjR (by omega)
        · simp only [hjB, ↓reduceDIte]
          let jw : Fin C.gates.length := ⟨w - 9, hs'⟩
          have hjw_notK : jw ∉ K := fun hk => hnc (Or.inr ⟨jw, hk, by dsimp [jw]; omega⟩)
          have hjw_R : jw ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => by
            rcases Finset.mem_union.mp h with h | h
            · exact hjw_notK h
            · exact hjB h⟩
          have hlt := hidx_mono jw j hjw_R hjR (by dsimp [jw]; omega)
          exact Nat.add_lt_add_left hlt 8
  have hres_bound : ∀ w < 9 + s, ¬ isConstW w → resolve w < 8 + m := by
    intro w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hnc
      dsimp only [resolve]; rw [resolveWire]
      by_cases h9 : w < 9
      · simp only [h9, ↓reduceDIte]; omega
      · have hs' : w - 9 < C.gates.length := by omega
        simp only [h9, hs', ↓reduceDIte]
        by_cases hjB : (⟨w - 9, hs'⟩ : Fin C.gates.length) ∈ B
        · simp only [hjB, ↓reduceDIte]
          have hspec := Classical.choose_spec (hB_bypass ⟨w - 9, hs'⟩ hjB)
          have hbw : byp ⟨w - 9, hs'⟩ hjB < w := by
            have := hbyp_lt ⟨w - 9, hs'⟩ hjB; dsimp at this; omega
          exact ih (byp ⟨w - 9, hs'⟩ hjB) hbw (by omega) hspec.2.1
        · simp only [hjB, ↓reduceDIte]
          let jw : Fin C.gates.length := ⟨w - 9, hs'⟩
          have hjw_notK : jw ∉ K := fun hk => hnc (Or.inr ⟨jw, hk, by dsimp [jw]; omega⟩)
          have hjw_R : jw ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => by
            rcases Finset.mem_union.mp h with h | h
            · exact hjw_notK h
            · exact hjB h⟩
          exact Nat.add_lt_add_left (hidx_lt jw hjw_R) 8
  have hR_no_const_in : ∀ j ∈ R, ∀ w ∈ (C.gates.get j).inputs, ¬ isConstW w := by
    intro j hjR w hw hcw
    have hj_notK : j ∉ K := fun hk => (Finset.mem_sdiff.mp hjR).2 (Finset.mem_union_left _ hk)
    have hj_notB : j ∉ B := fun hb => (Finset.mem_sdiff.mp hjR).2 (Finset.mem_union_right _ hb)
    exact hj_notB (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj_notK, w, hw, hcw⟩)
  let convOp : PEqualNP.CircuitLowerBounds.GateOp → Op
    | PEqualNP.CircuitLowerBounds.GateOp.and => Op.and
    | PEqualNP.CircuitLowerBounds.GateOp.or => Op.or
    | _ => Op.not
  let D : DAG m :=
    { nodes := fun i =>
        let j := Rlist.get i
        let g := C.gates.get j
        ⟨convOp g.op, resolve (g.inputs.getD 0 0), resolve (g.inputs.getD 1 0)⟩
      ha := fun i => by
        dsimp only
        let j := Rlist.get i
        have hjR : j ∈ R := (hRlist_mem j).mp (List.get_mem Rlist i)
        have hidx : idxOf j = i.val := hidx_get i
        rcases hform j with ⟨_, a, ha, hin⟩ | ⟨_, a, b, hab, hb, hin⟩
        · have ha_in : a ∈ (C.gates.get j).inputs := by rw [hin]; simp
          have hlt := hres_lt a (by omega) (hR_no_const_in j hjR a ha_in) j hjR ha
          change resolve ((C.gates.get j).inputs.getD 0 0) < 8 + i.val
          rw [hin]; simpa [hidx] using hlt
        · have ha_in : a ∈ (C.gates.get j).inputs := by rw [hin]; simp
          have hlt := hres_lt a (by omega) (hR_no_const_in j hjR a ha_in) j hjR (lt_trans hab hb)
          change resolve ((C.gates.get j).inputs.getD 0 0) < 8 + i.val
          rw [hin]; simpa [hidx] using hlt
      hb := fun i hop => by
        dsimp only at hop ⊢
        let j := Rlist.get i
        have hjR : j ∈ R := (hRlist_mem j).mp (List.get_mem Rlist i)
        have hidx : idxOf j = i.val := hidx_get i
        rcases hform j with ⟨hnot, _, _, _⟩ | ⟨_, a, b, _, hb, hin⟩
        · change convOp (C.gates.get j).op ≠ Op.not at hop
          rw [hnot] at hop; exact absurd rfl hop
        · have hb_in : b ∈ (C.gates.get j).inputs := by rw [hin]; simp
          have hlt := hres_lt b (by omega) (hR_no_const_in j hjR b hb_in) j hjR hb
          change resolve ((C.gates.get j).inputs.getD 1 0) < 8 + i.val
          rw [hin]; simpa [hidx] using hlt }
  have hD_sim : ∀ y : Fin 8 → Bool, ∀ w < 9 + s, ¬ isConstW w →
      D.val y (resolve w) = wval w y := by
    intro y w
    induction w using Nat.strongRecOn with
    | ind w ih =>
      intro hw hnc
      dsimp only [resolve]; rw [resolveWire]
      by_cases h9 : w < 9
      · simp only [h9, ↓reduceDIte]
        have hw_pos : 1 ≤ w := by
          by_contra h0; exact hnc (Or.inl (by omega))
        let i : Fin 8 := ⟨w - 1, by omega⟩
        rw [DAG.val_input D y i]
        have := hwval_in i y
        simpa [i, show 1 + (w - 1) = w by omega] using this.symm
      · have hs' : w - 9 < C.gates.length := by omega
        simp only [h9, hs', ↓reduceDIte]
        by_cases hjB : (⟨w - 9, hs'⟩ : Fin C.gates.length) ∈ B
        · simp only [hjB, ↓reduceDIte]
          have hspec := Classical.choose_spec (hB_bypass ⟨w - 9, hs'⟩ hjB)
          have hw_eq : w = 9 + (⟨w - 9, hs'⟩ : Fin C.gates.length).val := by dsimp; omega
          rw [ih _ (by have := hspec.1; dsimp at this; omega) (by have := hspec.1; dsimp at this; omega) hspec.2.1, ← hspec.2.2 y, ← hw_eq]
        · simp only [hjB, ↓reduceDIte]
          let j : Fin C.gates.length := ⟨w - 9, hs'⟩
          have hw_eq : w = 9 + j.val := by dsimp [j]; omega
          have hj_notK : j ∉ K := fun hk => hnc (Or.inr ⟨j, hk, hw_eq⟩)
          have hjR : j ∈ R := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => by
            rcases Finset.mem_union.mp h with h | h
            · exact hj_notK h
            · exact hjB h⟩
          let idx : Fin m := ⟨idxOf j, hidx_lt j hjR⟩
          have hget : Rlist.get idx = j := List.getElem_idxOf (hidx_lt j hjR)
          have hw_gate := hwval_gate j y
          rcases hform j with ⟨hop, a, ha, hin⟩ | ⟨hop, a, b, hab, hb, hin⟩
          · have ha_in : a ∈ (C.gates.get j).inputs := by rw [hin]; simp
            have hanc := hR_no_const_in j hjR a ha_in
            have hDop : (D.nodes idx).op = Op.not := by
              change convOp (C.gates.get (Rlist.get idx)).op = Op.not; rw [hget, hop]
            rw [show 8 + idxOf j = 8 + idx.val from rfl, DAG.val_gate_not D y idx hDop]
            have hDa : (D.nodes idx).a = resolve a := by
              change resolve ((C.gates.get (Rlist.get idx)).inputs.getD 0 0) = resolve a
              rw [hget, hin]; rfl
            rw [hDa, ih a (by omega) (by omega) hanc, hw_eq]
            rw [hop, hin] at hw_gate
            simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hw_gate.symm
          · have ha_in : a ∈ (C.gates.get j).inputs := by rw [hin]; simp
            have hb_in : b ∈ (C.gates.get j).inputs := by rw [hin]; simp
            have hanc := hR_no_const_in j hjR a ha_in
            have hbnc := hR_no_const_in j hjR b hb_in
            have hDa : (D.nodes idx).a = resolve a := by
              change resolve ((C.gates.get (Rlist.get idx)).inputs.getD 0 0) = resolve a
              rw [hget, hin]; rfl
            have hDb : (D.nodes idx).b = resolve b := by
              change resolve ((C.gates.get (Rlist.get idx)).inputs.getD 1 0) = resolve b
              rw [hget, hin]; rfl
            rcases hop with hop | hop
            · have hDop : (D.nodes idx).op = Op.and := by
                change convOp (C.gates.get (Rlist.get idx)).op = Op.and; rw [hget, hop]
              rw [show 8 + idxOf j = 8 + idx.val from rfl, DAG.val_gate_and D y idx hDop, hDa, hDb,
                ih a (by omega) (by omega) hanc, ih b (by omega) (by omega) hbnc, hw_eq]
              rw [hop, hin] at hw_gate
              simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hw_gate.symm
            · have hDop : (D.nodes idx).op = Op.or := by
                change convOp (C.gates.get (Rlist.get idx)).op = Op.or; rw [hget, hop]
              rw [show 8 + idxOf j = 8 + idx.val from rfl, DAG.val_gate_or D y idx hDop, hDa, hDb,
                ih a (by omega) (by omega) hanc, ih b (by omega) (by omega) hbnc, hw_eq]
              rw [hop, hin] at hw_gate
              simpa [PEqualNP.CircuitLowerBounds.GateOp.eval] using hw_gate.symm
  have hout_nc : ¬ isConstW (9 + (s - 1)) := by
    rintro (h0 | ⟨k, hk, heq⟩)
    · omega
    · have : k = ⟨s - 1, by omega⟩ := Fin.ext (by dsimp; omega)
      exact hjlast_notK (this ▸ hk)
  refine dag_no_le_eight m hm8 D (resolve (9 + (s - 1))) (hres_bound _ (by omega) hout_nc) fun y => ?_
  rw [hD_sim y (9 + (s - 1)) (by omega) hout_nc, hwval_out y]

end PEqualNP.Outside.L_meta_27373_aux

theorem PEqualNP.Outside.L_meta_27373 : (¬ (∃ C : PEqualNP.CircuitLowerBounds.Circuit,
    PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 12 ∧
    (∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = ((x 0 && x 4 && x 8) || (x 0 && x 5 && x 7) || (x 1 && x 3 && x 8) || (x 1 && x 5 && x 6) || (x 2 && x 3 && x 7) || (x 2 && x 4 && x 6))) ∧
    C.output + 1 = 9 + C.size ∧
    (∀ j : Fin C.gates.length,
      ((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧
          ∃ a, a < 9 + j.val ∧ (C.gates.get j).inputs = [a]) ∨
      (((C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
          (C.gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧
          ∃ a b, a < b ∧ b < 9 + j.val ∧ (C.gates.get j).inputs = [a, b])) ∧
    (∀ j : Fin C.gates.length,
      (∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn y)).getD (9 + j.val) false) ∧
      ∀ k, k < 9 + j.val → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD (9 + j.val) false ≠ (C.wires (List.ofFn x)).getD k false) ∧
    (∀ j : Fin C.gates.length, j.val + 1 < C.gates.length →
      ∃ k : Fin C.gates.length, j.val < k.val ∧ 9 + j.val ∈ (C.gates.get k).inputs) ∧
    C.gates.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 4]⟩ ∧
    C.gates.tail.head? = some ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 9]⟩)) :=
  PEqualNP.Outside.L_meta_27373_aux.main_refute
