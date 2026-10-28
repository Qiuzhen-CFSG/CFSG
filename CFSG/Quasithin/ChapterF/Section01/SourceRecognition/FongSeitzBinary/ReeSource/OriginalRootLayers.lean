module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCoordinates
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.ReeSource.OriginalCartan
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiRootLayers
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.ReeSource.SuzukiBarAction

/-!
# Original endpoint and Cartan applications of the Suzuki root layers

The injective original root lift identifies its literal image with the
source intersection. Transporting the actual Frattini quotient therefore
gives the additive field chart on that original image, with its parameter
formula. Squares and internal commutators retain the original endpoint
representatives; the generated-carrier specialization uses the same Q.q.
No finiteness of the original ambient group is required.

Pull back the barred-root action through the entire original Cartan. Its
kernel is precisely the original panel core, and a scalar on the bar forces
the proved k*pi(k) right-conjugation formula on Omega in the original
parabolic. The endpoint index i is arbitrary, so both marked inclusion
squares are retained. Positive parameters have Frattini equal to center;
at the binary parameter that containment is strict.

Source: Fong--Seitz I (1973), proof of (6H), pp.52--56, and II (1974),
§10, pp.221--224 and the root law preceding (10.32), p.230. These results
supply the literal root-layer and scalar-weight transports for the source
construction. The specific torus scalar values, four-space recognition,
mixed root equations, and final Chapter12 amalgam comparison remain open.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
open BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
open MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

def originalRootRangeEquiv : (originalRootLift Q e split i).range ≃* simpleRoot Q split i :=
  (MonoidHom.ofInjective (originalRootLift_injective Q e split i)).symm

def originalSuzukiFrattiniQuotientEquiv :
    ((originalRootLift Q e split i).range ⧸ frattini (originalRootLift Q e split i).range) ≃*
      Multiplicative (BinaryGaloisField (2*m+1)) :=
  (QuotientGroup.congr _ _ (originalRootRangeEquiv Q e split i)
    (frattini_map_equiv _)).trans (suzukiFrattiniQuotientEquiv Q split i m μ hB)

theorem originalSuzukiFrattiniQuotientEquiv_parameter (a b : BinaryGaloisField (2*m+1)) :
    originalSuzukiFrattiniQuotientEquiv Q e split i m μ hB
      (QuotientGroup.mk (⟨originalSuzukiParameter Q e split i m μ hB a b,
        ⟨suzukiParameter Q split i m μ hB a b,rfl⟩⟩ : (originalRootLift Q e split i).range)) =
      Multiplicative.ofAdd a := by
  change suzukiFrattiniQuotientEquiv Q split i m μ hB (QuotientGroup.mk
    ((MonoidHom.ofInjective (originalRootLift_injective Q e split i)).symm
      ((MonoidHom.ofInjective (originalRootLift_injective Q e split i))
        (suzukiParameter Q split i m μ hB a b)))) = _
  rw [MulEquiv.symm_apply_apply, suzukiFrattiniQuotientEquiv_parameter]

theorem originalSuzukiParameter_square_root (b : BinaryGaloisField (2*m+1)) :
    originalSuzukiParameter Q e split i m μ hB (suzukiTits m b / b) 0 ^ 2 =
      originalSuzukiParameter Q e split i m μ hB 0 b := by
  change (originalRootLift Q e split i (suzukiParameter Q split i m μ hB _ _))^2 = _
  rw [← map_pow, suzukiParameter_square_root]
  rfl

open scoped commutatorElement

theorem originalSuzukiParameter_commutator (a b c d : BinaryGaloisField (2*m+1)) :
    ⁅originalSuzukiParameter Q e split i m μ hB a b,
      originalSuzukiParameter Q e split i m μ hB c d⁆ =
        originalSuzukiParameter Q e split i m μ hB 0
          (a*suzukiTits m c+c*suzukiTits m a) := by
  change ⁅originalRootLift Q e split i (suzukiParameter Q split i m μ hB a b),
    originalRootLift Q e split i (suzukiParameter Q split i m μ hB c d)⁆ = _
  rw [← map_commutatorElement, suzukiParameter_commutator]
  rfl

include μ hB in
theorem originalSuzuki_frattini_quotient_card :
    Nat.card ((originalRootLift Q e split i).range ⧸
      frattini (originalRootLift Q e split i).range) = 2^(2*m+1) := by
  rw [Nat.card_congr (originalSuzukiFrattiniQuotientEquiv Q e split i m μ hB).toEquiv,
    Nat.card_congr Multiplicative.ofAdd.symm]
  exact GaloisField.card 2 (2*m+1) (by omega)

include μ hB in
theorem originalSuzuki_frattini_eq_center (hm : 0 < m) :
    frattini (originalRootLift Q e split i).range = center (originalRootLift Q e split i).range := by
  let f := originalRootRangeEquiv Q e split i
  apply map_injective (f := f.toMonoidHom) f.injective
  rw [frattini_map_equiv, center_map_equiv]
  exact suzuki_frattini_eq_center Q split i m μ hB hm

variable (μ₀ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup 0)
  (hB₀ : (quotientBorel Q i).map μ₀.toMonoidHom =
    normalizer (SuzukiRootSubgroup 0 : Set (SuzukiMatrixGroup 0)))

include μ₀ hB₀ in
theorem original_binary_suzuki_frattini_lt_center :
    frattini (originalRootLift Q e split i).range < center (originalRootLift Q e split i).range := by
  let f := originalRootRangeEquiv Q e split i
  apply (map_lt_map_iff_of_injective (f := f.toMonoidHom) f.injective).mp
  rw [frattini_map_equiv, center_map_equiv]
  exact binary_suzuki_frattini_lt_center Q split i μ₀ hB₀

variable (h : HypothesisF11 L S)

def originalSuzukiBarCartanAction : originalCartan Q e h →*
    MulAut (Multiplicative (BinaryGaloisField (2*m+1))) :=
  (suzukiBarCartanAction Q split i m μ hB).comp (originalCartanEquiv Q e h).toMonoidHom

theorem originalSuzukiBarCartanAction_kernel (a : originalCartan Q e h) :
    a ∈ (originalSuzukiBarCartanAction Q e split i m μ hB h).ker ↔
      (⟨a.val,commonBorel_le_parabolic i a.val.property⟩ : parabolic L S i) ∈
        originalPanelKernel (L := L) (S := S) i := by
  change originalCartanEquiv Q e h a ∈ (suzukiBarCartanAction Q split i m μ hB).ker ↔ _
  rw [suzukiBarCartanAction_kernel, cartanPanelMap_kernel]
  change (originalCartanEquiv Q e h a : X ⧸ Q.D) ∈ embeddedPanelKernel Q i ↔ _
  rw [← originalCartan_endpoint Q e h i a, ← originalPanelKernel_image Q e h i]
  have hf : Function.Injective (endpointMap Q e i) :=
    (Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective
  exact mem_map_iff_mem hf

theorem originalSuzukiBarCartanAction_card (s : RootReflection Q split i) :
    Nat.card (originalSuzukiBarCartanAction Q e split i m μ hB h).range = 2^(2*m+1)-1 := by
  have he : (originalCartanEquiv Q e h).toMonoidHom.range = ⊤ :=
    (originalCartanEquiv Q e h).toMonoidHom.range_eq_top_of_surjective
      (originalCartanEquiv Q e h).surjective
  rw [originalSuzukiBarCartanAction, MonoidHom.range_comp, he, ← MonoidHom.range_eq_map]
  exact suzukiBarCartanAction_card Q split i m μ hB s

theorem originalSuzukiOmega_scalar_right (a : originalCartan Q e h)
    (k : BinaryGaloisField (2*m+1))
    (hk : ∀ c, originalSuzukiBarCartanAction Q e split i m μ hB h a⁻¹
      (Multiplicative.ofAdd c) = Multiplicative.ofAdd (k*c))
    (b : BinaryGaloisField (2*m+1)) :
    let aP : parabolic L S i := ⟨a.val,commonBorel_le_parabolic i a.val.property⟩
    aP⁻¹ * originalSuzukiParameter Q e split i m μ hB 0 b * aP =
      originalSuzukiParameter Q e split i m μ hB 0 (k*suzukiTits m k*b) := by
  dsimp only
  apply ((Endpoint Q i).subtype_injective.comp (endpoint Q e i).injective)
  change endpointMap Q e i (_⁻¹ * _ * _) = endpointMap Q e i _
  rw [map_mul, map_mul, map_inv, originalCartan_endpoint Q e h i a]
  simp only [originalSuzukiParameter, originalRootLift_image]
  apply suzukiBarAction_scalar_omega_right Q split i m μ hB
    (inclusion (torus_normalizes_simpleRoot Q split i) (originalCartanEquiv Q e h a)) k
  intro c
  have hc := hk c
  change suzukiBarAction Q split i m μ hB
    (inclusion (torus_normalizes_simpleRoot Q split i) (originalCartanEquiv Q e h a⁻¹))
      (Multiplicative.ofAdd c) = _ at hc
  simpa only [map_inv] using hc

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource

@[expose] public noncomputable section
open Subgroup BenderSuzuki.MatrixGroups BenderSuzuki.PFAppendixIII
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.ReeSource
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
  (Q : SourceQuotient L S) (split : SplitData Q.tits) (i : Fin 2) (m : ℕ)
  (μ : (Endpoint Q i ⧸ panelKernel Q i) ≃* SuzukiMatrixGroup m)
  (hB : (quotientBorel Q i).map μ.toMonoidHom =
    normalizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)))

theorem originalSuzukiParameter_square_quotient (b : BinaryGaloisField (2*m+1)) :
    Q.q ((⟨originalSuzukiParameter Q (originalMarkedIso Q) split i m μ hB
        (suzukiTits m b / b) 0,
      parabolic_le_generated i (originalSuzukiParameter Q (originalMarkedIso Q) split i m μ hB
        (suzukiTits m b / b) 0).property⟩ : generated L S)^2) =
      (suzukiParameter Q split i m μ hB 0 b : (generated L S) ⧸ Q.D) := by
  rw [map_pow, originalSuzukiParameter_quotient, ← Subgroup.coe_pow, suzukiParameter_square_root]

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.ReeSource
