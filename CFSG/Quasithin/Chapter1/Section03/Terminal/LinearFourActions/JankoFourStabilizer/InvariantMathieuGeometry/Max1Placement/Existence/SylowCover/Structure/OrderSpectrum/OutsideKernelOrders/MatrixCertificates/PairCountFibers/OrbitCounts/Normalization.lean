module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Certificate

/-!
# Canonical planes and bounded finite verification

Independent ordered pairs share one canonical plane. Normalization preserves
the step certificate, so the expensive conjugation check is performed once per
plane. The finite-domain lemma assembles blocks of sixteen coordinates without
omitting any point. Dependent pairs are handled separately, since sorting them
need not be idempotent.
Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers

def orbitNormalizationCheck (i : Fin 9) (a b : Fin (candidateOrder i)) : Bool :=
  let p := orbitPlane i a b
  if orbitDependent i a b then true else
    decide (orbitPlane i p.1 p.2 = p ∧ ¬ orbitDependent i p.1 p.2)

def orbitCanonicalCheck (i : Fin 9) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (a b : Fin (candidateOrder i)) : Bool :=
  if orbitPlane i a b = (a,b) then orbitCheck i left right values action data a b else true

theorem orbitStep_of_canonical_check (i : Fin 9) {t : ℕ} [NeZero t]
    (left right : Fin t → Fin (candidateOrder i)) (values : Fin t → ℕ)
    (action : Fin 21 → Fin (candidateOrder i) → Fin (candidateOrder i))
    (data : Fin (candidateOrder i) → Fin (candidateOrder i) → ℕ)
    (hcheck : ∀ a b, orbitCanonicalCheck i left right values action data a b = true)
    (a b : Fin (candidateOrder i)) (hn : orbitNormalizationCheck i a b = true) :
    OrbitStep i left right values action data a b := by
  let p := orbitPlane i a b
  by_cases hd : orbitDependent i a b
  · simp only [OrbitStep, if_pos hd]
  have hn' := hn
  simp only [orbitNormalizationCheck, if_neg hd] at hn'
  have hp : orbitPlane i p.1 p.2 = p ∧ ¬ orbitDependent i p.1 p.2 := of_decide_eq_true hn'
  have hnp : ¬ orbitDependent i p.1 p.2 := hp.2
  have hc := hcheck p.1 p.2
  have hid : orbitPlane i p.1 p.2 = (p.1,p.2) := hp.1
  rw [orbitCanonicalCheck, if_pos hid] at hc
  have hs := orbitStep_of_check i left right values action data p.1 p.2 hc
  have hw : orbitCode i data p.1 p.2 = orbitCode i data a b := by
    unfold orbitCode
    rw [hp.1]
  have ht : orbitTable i values data p.1 p.2 = orbitTable i values data a b := by
    simp only [orbitTable, if_neg hnp, if_neg hd, hw]
  simp only [OrbitStep, if_neg hnp, if_neg hd] at hs ⊢
  rw [hw, hp.1, ht] at hs
  exact hs
/-- Assemble bounded checks on blocks of sixteen coordinates into a complete
finite-domain assertion. No coordinate is dropped at a block boundary. -/
theorem orbit_forall_blocks {q : ℕ} (P : Fin (16*q) → Prop)
    (h : ∀ j : Fin q, ∀ k : Fin 16,
      P ⟨16*j.val+k.val, by have := j.isLt; have := k.isLt; omega⟩) : ∀ a, P a := by
  intro a
  let j : Fin q := ⟨a.val / 16, by have := a.isLt; omega⟩
  let k : Fin 16 := ⟨a.val % 16, Nat.mod_lt _ (by decide)⟩
  have he : a = (⟨16*j.val+k.val, by have := j.isLt; have := k.isLt; omega⟩ : Fin (16*q)) := by
    apply Fin.ext
    dsimp [j,k]
    omega
  rw [he]
  exact h j k
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
