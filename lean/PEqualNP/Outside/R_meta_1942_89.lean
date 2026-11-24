import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_1942_89 :
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 →
      let E := (Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)
      let single : Fin N × Fin N → Bool := fun e =>
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => N.ble i) e.1.val (N + e.2.val) ||
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => !(N.ble i)) e.1.val (N + e.2.val)
      (E.filter (fun e => single e = true)).card ≤ 50 * C.size) →
    (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, Fintype.card {p : Fin N // I p l} = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      PEqualNP.TopForm.IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
            z (Fin.natAdd N l) = true) →
      PEqualNP.ReadK.IsReadK (N + N) C 2 →
      let E := (Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)
      let single : Fin N × Fin N → Bool := fun e =>
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => N.ble i) e.1.val (N + e.2.val) ||
        PEqualNP.ReadK.lineSingle C (N + N) (fun i => !(N.ble i)) e.1.val (N + e.2.val)
      (E.filter (fun e => single e = false)).card ≤ 50 * C.size) →
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → PEqualNP.ReadK.IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  intro singleCharge doubleCharge q N I inst C hq hN hlines hpairs hAO heval hread
  let E := (Finset.univ : Finset (Fin N × Fin N)).filter (fun e => I e.1 e.2)
  let single : Fin N × Fin N → Bool := fun e =>
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => N.ble i) e.1.val (N + e.2.val) ||
    PEqualNP.ReadK.lineSingle C (N + N) (fun i => !(N.ble i)) e.1.val (N + e.2.val)
  have hchar : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true := by
    intro z
    rw [heval z]
    simp only [decide_eq_true_eq]
  have hs : (E.filter (fun e => single e = true)).card ≤ 50 * C.size :=
    singleCharge q N I C hq hN
      (fun l => by simpa only [Fintype.card_subtype] using hlines l) hpairs hAO hchar hread
  have hd : (E.filter (fun e => single e = false)).card ≤ 50 * C.size :=
    doubleCharge q N I C hq hN
      (fun l => by simpa only [Fintype.card_subtype] using hlines l) hpairs hAO hchar hread
  have hE : E.card = N * (q + 1) := by
    calc
      E.card = ∑ e : Fin N × Fin N, if I e.1 e.2 then 1 else 0 := by
        exact Finset.card_filter _ _
      _ = ∑ p : Fin N, ∑ l : Fin N, if I p l then 1 else 0 := by
        rw [Fintype.sum_prod_type]
      _ = ∑ l : Fin N, ∑ p : Fin N, if I p l then 1 else 0 := Finset.sum_comm
      _ = ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
        apply Finset.sum_congr rfl
        intro l hl
        exact (Finset.card_filter _ _).symm
      _ = N * (q + 1) := by simp [hlines]
  have split := Finset.card_filter_add_card_filter_not (s := E) (fun e => single e = true)
  have hfilter : (E.filter (fun e => ¬ single e = true)) =
      E.filter (fun e => single e = false) := by
    apply Finset.filter_congr
    intro e he
    cases single e <;> simp
  rw [hfilter] at split
  have total : E.card ≤ 100 * C.size := by
    omega
  exact (Nat.mul_le_mul_left N (Nat.le_succ q)).trans (hE ▸ total)
