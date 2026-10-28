module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand.Exceptional.Seven
public import Theory.GroupAction.FiveSevenCentralizer
public import Theory.GroupTheory.Commutator.RelativeGeneration

/-!
# The seven-residual on the literal central core section

An automorphism trivial on A/O₂(A) centralizes the inner action of A on
E=O₂(A)/(Z(A) intersect O₂(A)), provided [O₂(A),O₂(A)]≤Z(A).
If |E|=256 and an inner subgroup of order five is fixed-point-free, its
centralizer in Aut(E) has order prime to seven. Combining this with the
top quotient kills the seven-residual on E. Triviality on E preserves
UZ(A); taking its commutator with A recovers U when [U,A]=U.

The final two theorems apply this argument to A=L₁ and the original seed
V, using the proved exceptional quotient action and Y=O^{7′}(Y)(Y∩M).
They reduce the SL₃ branch of 11.1.5 to the literal two-natural-factor
calculation. That calculation, the Sp₄ branch, fixed-center centralizer
control and final assembly remain with qt-d-1222-natural-point-fixed-summand.
Only the preceding rank-one quotient and fixed-line identities have external
owners (qt-d-1222-natural-flag-cartan and its normalizer-source parent).
No source theorem is asserted with these remaining block inputs discharged.

Source: Aschbacher–Smith, combined manuscript, 1 March 2004,
11.1.5, printed p.766. The fixed-free-five argument supplies an elementary
alternative to the source's semilinear automorphism-group bound.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement
open Representation.BinaryOffender Representation.GoldschmidtONan
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
variable {G : Type*} [Group G]

/-- The literal section O₂(A)/(Z(A) intersect O₂(A)). -/
abbrev CoreCentralSection (A : Subgroup G) :=
  pCore 2 A ⧸ (center A).subgroupOf (pCore 2 A)

namespace ChiefSection
variable (A : Subgroup G)

theorem center_map (α : MulAut A) :
    ((center A).subgroupOf (pCore 2 A)).map
      (MulAut.characteristic (pCore 2 A) α).toMonoidHom =
      (center A).subgroupOf (pCore 2 A) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (centerCongr α ⟨y, hy⟩).property
  · intro hx
    refine ⟨MulAut.characteristic (pCore 2 A) α.symm x, ?_, ?_⟩
    · exact (centerCongr α.symm ⟨x, hx⟩).property
    · apply Subtype.ext
      exact α.apply_symm_apply x

/-- Restriction followed by the original central quotient; no Frattini
quotient or changed representation is used. -/
def automorphismAction : MulAut A →* MulAut (CoreCentralSection A) where
  toFun α := QuotientGroup.congr _ _ (MulAut.characteristic (pCore 2 A) α)
    (center_map A α)
  map_one' := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with | h x => rfl
  map_mul' α β := by
    apply MulEquiv.ext
    intro x
    induction x using Quotient.inductionOn with | h x => rfl

@[simp] theorem automorphismAction_mk (α : MulAut A) (x : pCore 2 A) :
    automorphismAction A α (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ (MulAut.characteristic (pCore 2 A) α x) := rfl

/-- The inner A-action on the same section. -/
def innerAction : A →* MulAut (CoreCentralSection A) :=
  (automorphismAction A).comp MulAut.conj

/-- The ambient normalizer action on the same section. -/
def normalizerAction : normalizer (A : Set G) →* MulAut (CoreCentralSection A) :=
  (automorphismAction A).comp A.normalizerMonoidHom

private theorem inner_kills_core
    (hc : ⁅pCore 2 A, pCore 2 A⁆ ≤ center A) :
    pCore 2 A ≤ (innerAction A).ker := by
  intro a ha
  apply MonoidHom.mem_ker.mpr
  apply MulEquiv.ext
  intro x
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective ((center A).subgroupOf (pCore 2 A)) x
  apply QuotientGroup.eq_iff_div_mem.mpr
  change a * (q : A) * a⁻¹ / (q : A) ∈ center A
  simpa only [commutatorElement_def, div_eq_mul_inv] using
    hc (commutator_mem_commutator ha q.property)

private theorem kernel_centralizes_inner
    (hc : ⁅pCore 2 A, pCore 2 A⁆ ≤ center A) :
    (quotientAut (pCore 2 A)).ker.map (automorphismAction A) ≤
      centralizer ((innerAction A).range : Set _) := by
  rintro _ ⟨α, hα, rfl⟩
  apply mem_centralizer_iff.mpr
  rintro _ ⟨x, rfl⟩
  let lift := QuotientGroup.lift (pCore 2 A) (innerAction A) (inner_kills_core A hc)
  have heq : QuotientGroup.mk' (pCore 2 A) (α x) =
      QuotientGroup.mk' (pCore 2 A) x := by
    have h := DFunLike.congr_fun (show quotientAut (pCore 2 A) α = 1 from hα)
      (QuotientGroup.mk' (pCore 2 A) x)
    rw [quotientAut_apply_mk] at h
    exact h
  have hsame : innerAction A (α x) = innerAction A x := congrArg lift heq
  have hconj : α * MulAut.conj x * α⁻¹ = MulAut.conj (α x) := by
    apply MulEquiv.ext
    intro z
    change α (x * α.symm z * x⁻¹) = α x * z * (α x)⁻¹
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
  have h := congrArg (automorphismAction A) hconj
  simp only [map_mul, map_inv] at h
  change automorphismAction A α * innerAction A x *
      (automorphismAction A α)⁻¹ = innerAction A (α x) at h
  rw [hsame] at h
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

variable [Finite G]

/-- Two natural four-dimensional binary factors give a section of order
256. A fixed-free five-subgroup then makes its centralizer seven-free.
Together with the top quotient, this kills the seven-residual on the
literal central section. -/
theorem sevenResidual_le_section_kernel
    {Y : Type*} [Group Y] (a : Y →* MulAut A)
    (hq : Nat.Coprime 7 (Nat.card ((quotientAut (pCore 2 A)).comp a).range))
    (hc : ⁅pCore 2 A, pCore 2 A⁆ ≤ center A)
    (hcard : Nat.card (CoreCentralSection A) = 256)
    (B : Subgroup (MulAut (CoreCentralSection A)))
    (hB : B ≤ (innerAction A).range) (hBcard : Nat.card B = 5)
    (hfixed : FixedPoints.subgroup B (CoreCentralSection A) = ⊥) :
    primeToResidual 7 Y ≤ ((automorphismAction A).comp a).ker := by
  let q := (quotientAut (pCore 2 A)).comp a
  let s := (automorphismAction A).comp a
  have hle : q.ker.map s ≤ centralizer (B : Set _) := by
    rintro _ ⟨y, hy, rfl⟩
    exact (centralizer_le hB) (kernel_centralizes_inner A hc
      (mem_map_of_mem (automorphismAction A) (show a y ∈ (quotientAut (pCore 2 A)).ker from hy)))
  have hk : Nat.Coprime 7 (Nat.card (q.ker.map s)) :=
    (Theory.GroupAction.seven_coprime_centralizer_of_fixed_free_five
      hcard B hBcard hfixed).coprime_dvd_right (card_dvd_of_le hle)
  have hi : Nat.Coprime 7 (s.ker ⊓ q.ker).index := by
    rw [← relIndex_mul_index (show s.ker ⊓ q.ker ≤ q.ker from inf_le_right),
      inf_relIndex_right, relIndex_ker, index_ker]
    exact hk.mul_right hq
  apply primeToResidual_le
  exact hi.coprime_dvd_right (index_dvd_of_le inf_le_left)

/-- Trivial action on O₂(A)/Z(A) preserves UZ(A), for U≤O₂(A).
Taking its commutator with A recovers U whenever [U,A]=U. -/
theorem normalizes_of_section_kernel {U : Subgroup G}
    (hU : U ≤ A.pCoreIn 2) (hfull : ⁅U,A⁆ = U)
    (y : normalizer (A : Set G)) (hy : y ∈ (normalizerAction A).ker) :
    (y : G) ∈ normalizer (U : Set G) := by
  let Z := (center A).map A.subtype
  let W := U ⊔ Z
  have hyZ : (y : G) ∈ normalizer (Z : Set G) :=
    normalizer_le_normalizer_characteristic_image A (center A) y.property
  have hyU : U.map (MulAut.conj (y : G)).toMonoidHom ≤ W := by
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨q, hq, hqu⟩ := hU hu
    let q' : pCore 2 A := ⟨q,hq⟩
    have h := DFunLike.congr_fun (show normalizerAction A y = 1 from hy)
      (QuotientGroup.mk' ((center A).subgroupOf (pCore 2 A)) q')
    change QuotientGroup.mk' _ (MulAut.characteristic (pCore 2 A)
      (A.normalizerMonoidHom y) q') = QuotientGroup.mk' _ q' at h
    have hz0 := QuotientGroup.eq_iff_div_mem.mp h
    have hz : (A.normalizerMonoidHom y) q / q ∈ center A := hz0
    have hzG : (y : G) * (q : G) * (y : G)⁻¹ / (q : G) ∈ Z :=
      mem_map_of_mem A.subtype hz
    have hw := W.mul_mem ((le_sup_right : Z ≤ W) hzG)
      ((le_sup_left : U ≤ W) (hqu ▸ hu))
    change ((y : G) * (q : G) * (y : G)⁻¹ / (q : G)) * (q : G) ∈ W at hw
    rw [div_mul_cancel] at hw
    change (y : G) * u * (y : G)⁻¹ ∈ W
    exact hqu ▸ hw
  have hyW : (y : G) ∈ normalizer (W : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rw [Subgroup.map_sup, mem_normalizer_iff_map_conj_eq.mp hyZ]
      exact sup_le hyU le_sup_right
    · rw [card_map_of_injective (MulAut.conj (y : G)).injective]
  have hZA : Z ≤ centralizer (A : Set G) := by
    rintro _ ⟨z,hz,rfl⟩ a ha
    exact congrArg Subtype.val ((mem_center_iff.mp hz) ⟨a,ha⟩)
  have hZU : Z ≤ normalizer (U : Set G) :=
    (hZA.trans (centralizer_le (hU.trans (pCoreIn_le 2 A)))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcomm : ⁅W,A⁆ = U := by
    apply le_antisymm
    · exact commutator_sup_le_of_relative_normal (normalizer (U : Set G))
        U Z A U le_rfl U.le_normalizer hZU hfull.le
        ((commutator_eq_bot_iff_le_centralizer.mpr hZA).le.trans bot_le)
    · calc U = ⁅U,A⁆ := hfull.symm
           _ ≤ ⁅W,A⁆ := commutator_mono le_sup_left le_rfl
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [← hcomm, map_commutator, mem_normalizer_iff_map_conj_eq.mp hyW,
    mem_normalizer_iff_map_conj_eq.mp y.property]

end ChiefSection
variable [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem seed_le_first_core_of_commutator (hfull : ⁅V,f.Li 0⁆ = V) :
    V ≤ (f.Li 0).pCoreIn 2 := by
  let := D.elementary
  apply le_pCoreIn_of_normalizes (IsElementaryAbelian.isPGroup 2 V)
  · exact hfull.ge.trans (le_normalizer_iff_commutator_le_right.mp
      (D.le_sylow.trans (f.sylow_normalizes_Li 0)))
  · exact ((localResidual_le _).trans inf_le_left).trans D.normalizes

/-- The central-section calculation on the literal first residual proves
that O^{7′}(Y) preserves the original seed. The remaining section inputs
are the two natural SL₃(4) chief factors, retained by this task. -/
theorem chosen_exceptional_sevenResidual_normalizes_seed_of_sections
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (X : Subgroup G)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hc : ⁅pCore 2 (f.Li 0), pCore 2 (f.Li 0)⁆ ≤ center (f.Li 0))
    (hcard : Nat.card (CoreCentralSection (f.Li 0)) = 256)
    (B : Subgroup (MulAut (CoreCentralSection (f.Li 0))))
    (hB : B ≤ (ChiefSection.innerAction (f.Li 0)).range)
    (hBcard : Nat.card B = 5)
    (hBfixed : FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥)
    (hfull : ⁅V,f.Li 0⁆ = V) :
    (primeToResidual 7 (normalizer (f.Ri 0 : Set G))).map
      (normalizer (f.Ri 0 : Set G)).subtype ≤ normalizer (V : Set G) := by
  have hn := chosen_exceptional_normalizes_first D S f hm hfix X hcenter hfixed he
  let a := (f.Li 0).normalizerMonoidHom.comp (inclusion hn)
  have hq : Nat.Coprime 7
      (Nat.card ((quotientAut (pCore 2 (f.Li 0))).comp a).range) := by
    have htop : Nat.Coprime 7 (Nat.card (MulAut (f.Li 0 ⧸ pCore 2 (f.Li 0)))) := by
      rw [exceptional_first_automorphism_card D S f hm X hcenter hfixed he]
      decide
    exact htop.coprime_dvd_right (card_subgroup_dvd_card _)
  have hk := ChiefSection.sevenResidual_le_section_kernel (f.Li 0) a hq hc
    hcard B hB hBcard hBfixed
  rintro _ ⟨y,hy,rfl⟩
  exact ChiefSection.normalizes_of_section_kernel (f.Li 0)
    (seed_le_first_core_of_commutator D S f hfull) hfull
    (inclusion hn y) (hk hy)

/-- Application to the source SL₃ contradiction. The original residual
generation Y=O^{7′}(Y)(Y∩M) and seed normalizer control discharge the
ambient conclusion once the literal two-factor calculation is supplied. -/
theorem chosen_exceptional_escape_of_sections
    (hm : ClassicalGroup.IsPSL (f.Li 0 ⧸ pCore 2 (f.Li 0)) 2 (2 ^ S.field.degree))
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (X : Subgroup G)
    (hescape : ¬ normalizer (f.Ri 0 : Set G) ≤ normalizer (L : Set G))
    (hspan : V = Source.conjugateSpan (normalizer (L : Set G)) V)
    (hcenter : radicalOmegaCenter (f.Ri 0) = f.Vi 0 ⊔ radicalFixedCenter (f.Ri 0) L)
    (h : Input (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hfixed : fixedSpace (representation (f.Ri 0)) (cartanImage (f.Ri 0) X) =
      fixedSubspace (f.Ri 0) L)
    (he : ExceptionalCase (representation (f.Ri 0)) (cartanImage (f.Ri 0) X))
    (hc : ⁅pCore 2 (f.Li 0), pCore 2 (f.Li 0)⁆ ≤ center (f.Li 0))
    (hcard : Nat.card (CoreCentralSection (f.Li 0)) = 256)
    (B : Subgroup (MulAut (CoreCentralSection (f.Li 0))))
    (hB : B ≤ (ChiefSection.innerAction (f.Li 0)).range)
    (hBcard : Nat.card B = 5)
    (hBfixed : FixedPoints.subgroup B (CoreCentralSection (f.Li 0)) = ⊥)
    (hfull : ⁅V,f.Li 0⁆ = V) : False := by
  exact hescape ((chosen_exceptional_normalizes_seed_of_sevenResidual D S f X
    hspan h hfixed he (chosen_exceptional_sevenResidual_normalizes_seed_of_sections
      D S f hm hfix X hcenter hfixed he hc hcard B hB hBcard hBfixed hfull)).trans
      (chosen_seed_normalizer_le D S))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.FixedSummand
