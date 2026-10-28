module
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion.MarkedTorus
public import Theory.SpecificGroups.SU3.EvenSemilinear.Geometry
import all Theory.SpecificGroups.SU3.EvenSemilinear.Geometry
public import Theory.GroupTheory.SylowNormalIntersection

/-!
# The five-torus for the actual unitary pair

The doubly transitive unitary root action places any two distinct Sylow
subgroups in one simultaneous coordinate system. Their centers therefore
form the actual marked pair centralized by the norm-one torus of order five.
In the source quotient H/O₂(H), the first Sylow subgroup is chosen to be
the intersection of the original Sylow image with O²(H/O₂(H)). This keeps
its normalizer above the original Sylow image. H-star minimality then puts
the torus in the image of the original local subgroup.

The coordinate, center and placement premises of the earlier MarkedTorus
interface are proved here. NonFFSourceMathieuM24Unitary supplies the literal
chosen-module application, including the lift and centralizer contradiction.
The private geometry import reuses its proved root action internally.
Source: Aschbacher--Smith 8.2.9, printed p.720, refs/quasithin.pdf;
unitary root geometry: Huppert II.10.12.
-/

public noncomputable section
open Subgroup BenderSuzuki.External BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus HermitianForm.BorelTorus.EvenCenterAction HermitianForm.EvenInner HermitianForm.MarkedFiveTorus
open HermitianForm.OddPrimeSylow.NormalizedOuter.Coverage
set_option backward.isDefEq.respectTransparency false
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuUnitary
variable {E : Type*} [Field E] [Finite E] [CharP E 2]
  (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
  (hcard : Nat.card E = 16) (hconj : ∀ x : E, J.conj x = x^4)

private instance : Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

include hJ hcard hconj
/-- One inner coordinate change places both of the specified Sylow groups. -/
theorem sylow_pair_coordinates
    (P Q : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) (hne : P ≠ Q) :
    ∃ k : ProjectiveSpecialUnitaryMatrixGroup J,
      (projectiveRoot J hJ).map (MulAut.conj k).toMonoidHom = P ∧
      (standardPair J hJ).map (MulAut.conj k).toMonoidHom =
        (center P).map (P : Subgroup _).subtype ⊔
        (center Q).map (Q : Subgroup _).subtype := by
  have hfixed : Nat.card {x : E // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  let P₀ := HermitianForm.EvenTwoRank.rootSylow J hJ (n := 2) (by decide) hcard hfixed
  let U := rootGroup J hJ
  let w := weyl J hJ
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P₀ P
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) P₀ Q
  have hg' : U.map (MulAut.conj g).toMonoidHom = P := congrArg Sylow.toSubgroup hg
  have hh' : U.map (MulAut.conj h).toMonoidHom = Q := congrArg Sylow.toSubgroup hh
  obtain ⟨ρ,α,_,hnorm,_,htwo⟩ := HermitianForm.EvenSemilinear.root_action J hJ 4 hcard hfixed
  have hp : ρ g α ≠ ρ h α := by
    intro he
    apply hne
    apply Sylow.ext
    rw [←hg',←hh']
    exact HermitianForm.EvenSemilinear.conjugate_eq_of_point_eq ρ U α hnorm g h he
  have hw : α ≠ ρ w α := by
    intro he
    apply rootGroup_ne_oppositeRootGroup J hJ (by decide : 1 < 4) hcard hfixed
    rw [oppositeRootGroup_eq_map]
    exact (hnorm w he.symm).symm
  obtain ⟨k,hkP,hkQ⟩ := htwo α (ρ w α) (ρ g α) (ρ h α) hw hp
  have hkU : U.map (MulAut.conj k).toMonoidHom = P := by
    rw [←hg']
    exact HermitianForm.EvenSemilinear.conjugate_eq_of_point_eq ρ U α hnorm k g hkP
  have hkV : (oppositeRootGroup J hJ).map (MulAut.conj k).toMonoidHom = Q := by
    rw [oppositeRootGroup_eq_map,HermitianForm.EvenSemilinear.map_conj_mul,←hh']
    apply HermitianForm.EvenSemilinear.conjugate_eq_of_point_eq ρ U α hnorm (k*w) h
    simpa only [map_mul,Equiv.Perm.mul_apply] using hkQ
  have hc := HermitianForm.NormalizedRootCentralizers.root_center J (n := 2)
    (by decide) hcard hfixed hJ
  have hcp : (centralImage J hJ).map (MulAut.conj k).toMonoidHom =
      (center P).map (P : Subgroup _).subtype := by
    rw [←hc,map_embeddedCenter _ _ (MulAut.conj k).injective]
    exact congrArg (fun A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) =>
      (center A).map A.subtype) hkU
  have hcq : ((centralImage J hJ).map (MulAut.conj (hermitianWeylPSU J hJ)).toMonoidHom).map
      (MulAut.conj k).toMonoidHom = (center Q).map (Q : Subgroup _).subtype := by
    rw [←hc,map_embeddedCenter _ _ (MulAut.conj (hermitianWeylPSU J hJ)).injective,
      map_embeddedCenter _ _ (MulAut.conj k).injective]
    rw [show (projectiveRoot J hJ).map (MulAut.conj (hermitianWeylPSU J hJ)).toMonoidHom =
      oppositeRootGroup J hJ from (oppositeRootGroup_eq_map J hJ).symm]
    exact congrArg (fun A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) =>
      (center A).map A.subtype) hkV
  exact ⟨k,hkU,by rw [standardPair,Subgroup.map_sup,hcp,hcq]⟩


variable {H : Type*} [Group H] [Finite H]

include hJ hcard hconj
omit [CharP E 2] in
/-- The first Sylow center is taken in the original Sylow intersection. -/
theorem quotient_pair_centers_at_sylow
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (T : Sylow 2 H) (V I : Subgroup H) [IsElementaryAbelian 2 V]
    (h : H) (hh : h ∈ I) (hVT : V ≤ T)
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hfour : Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) = 4)
    (hI : I.map (QuotientGroup.mk' (pCore 2 H)) ≤ pResidual 2 (H ⧸ pCore 2 H)) :
    let L := pResidual 2 (H ⧸ pCore 2 H)
    let q := QuotientGroup.mk' (pCore 2 H)
    ∃ P Q : Sylow 2 L,
      (P : Subgroup L).map L.subtype = (T : Subgroup H).map q ⊓ L ∧
      ((center P).map (P : Subgroup L).subtype).map L.subtype = V.map q ∧
      ((center Q).map (Q : Subgroup L).subtype).map L.subtype =
        (V.map (MulAut.conj h⁻¹).toMonoidHom).map q ∧
      I.map q = (((center P).map (P : Subgroup L).subtype) ⊔
        ((center Q).map (Q : Subgroup L).subtype)).map L.subtype := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let L := pResidual 2 (H ⧸ pCore 2 H)
  let S := T.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_normal L
  have hVL : V.map q ≤ L := (map_mono (show V ≤ I from hgen ▸ le_sup_left)).trans hI
  let A := (V.map q).subgroupOf L
  let : IsElementaryAbelian 2 (V.map q) := IsElementaryAbelian.map q
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf hVL
  have hAcard : Nat.card A = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv).trans hfour
  have hAP : A ≤ (P : Subgroup L) := by
    rw [hP]
    intro a ha
    exact (map_mono hVT) ha
  have hfixed : Nat.card {x : E // J.conj x = x} = 4 :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 2 (by decide) hcard hconj
  obtain ⟨hcenter,_,hsize⟩ := HermitianForm.SylowOmega.omega_of_projective_equiv
    J (n := 2) (by decide) hcard hfixed hJ e P
  have hAC : A = (center P).map (P : Subgroup L).subtype := by
    rw [←hcenter]
    apply eq_of_le_of_card_ge
    · exact (omegaOneAmbient_eq_self A).symm.le.trans (omegaOneAmbient_mono hAP)
    · simpa [hAcard] using hsize.le
  let g : L := ⟨q h⁻¹,hI (mem_map_of_mem q (I.inv_mem hh))⟩
  let Q := P.mapSurjective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).surjective
  have hfirst : ((center P).map (P : Subgroup L).subtype).map L.subtype = V.map q := by
    rw [←hAC]
    exact map_subgroupOf_eq_of_le hVL
  have hcomp : L.subtype.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (q h⁻¹)).toMonoidHom.comp L.subtype := by ext x; rfl
  have hqcomp : (MulAut.conj (q h⁻¹)).toMonoidHom.comp q =
      q.comp (MulAut.conj h⁻¹).toMonoidHom := by
    ext x
    change q h⁻¹ * q x * (q h⁻¹)⁻¹ = q (h⁻¹ * x * (h⁻¹)⁻¹)
    simp only [map_mul,map_inv]
  have hsecond : ((center Q).map (Q : Subgroup L).subtype).map L.subtype =
      (V.map (MulAut.conj h⁻¹).toMonoidHom).map q := by
    change ((center ((P : Subgroup L).map (MulAut.conj g).toMonoidHom)).map
      ((P : Subgroup L).map (MulAut.conj g).toMonoidHom).subtype).map L.subtype = _
    rw [←map_embeddedCenter _ _ (MulAut.conj g).injective,map_map,hcomp,
      ←map_map,hfirst,map_map,hqcomp,←map_map]
  refine ⟨P,Q,?_,hfirst,hsecond,?_⟩
  · rw [hP,subgroupOf_map_subtype]
    rfl
  · rw [Subgroup.map_sup,hfirst,hsecond,←Subgroup.map_sup,hgen]


open Chapter8.Section02.Normalizer.ParabolicReduction.UnitaryExclusion

include hJ hcard hconj
/-- Construct the quotient five-torus, with its placement in the original local image. -/
theorem exists_quotient_five_of_pair
    (e : pResidual 2 (H ⧸ pCore 2 H) ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (T : Sylow 2 H) (M V I : Subgroup H) [IsElementaryAbelian 2 V]
    (h : H) (hh : h ∈ I) (hVT : V ≤ T)
    (hgen : V ⊔ V.map (MulAut.conj h⁻¹).toMonoidHom = I)
    (hfour : Nat.card (V.map (QuotientGroup.mk' (pCore 2 H))) = 4)
    (hI : I.map (QuotientGroup.mk' (pCore 2 H)) ≤ pResidual 2 (H ⧸ pCore 2 H))
    (hInot : ¬ IsPGroup 2 (I.map (QuotientGroup.mk' (pCore 2 H))))
    (hlocal : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y ≠ ⊤ → Y ≤ M) :
    ∃ X : Subgroup (H ⧸ pCore 2 H), Nat.card X = 5 ∧
      X ≤ M.map (QuotientGroup.mk' (pCore 2 H)) ∧
      X ≤ centralizer (I.map (QuotientGroup.mk' (pCore 2 H)) : Set (H ⧸ pCore 2 H)) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let L := pResidual 2 (H ⧸ pCore 2 H)
  obtain ⟨P,Q,hP,hfirst,hsecond,hpair⟩ :=
    quotient_pair_centers_at_sylow J hJ hcard hconj e T V I h hh hVT hgen hfour hI
  have hne : P ≠ Q := by
    intro he
    subst Q
    rw [sup_idem] at hpair
    apply hInot
    have hle : I.map q ≤ (P : Subgroup L).map L.subtype := by
      rw [hpair]
      exact map_mono (map_subtype_le _)
    exact (P.isPGroup'.map L.subtype).to_le hle
  let P' := P.mapSurjective (f := e.toMonoidHom) e.surjective
  let Q' := Q.mapSurjective (f := e.toMonoidHom) e.surjective
  have hne' : P' ≠ Q' := by
    intro he
    apply hne
    apply Sylow.ext
    exact map_injective e.injective (congrArg Sylow.toSubgroup he)
  obtain ⟨k,hkRoot,hkPair⟩ := sylow_pair_coordinates J hJ hcard hconj P' Q' hne'
  let e' := e.trans (MulAut.conj k).symm
  have hc : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id L := by
    apply MonoidHom.ext
    intro x
    exact e.symm_apply_apply x
  have hr : (projectiveRoot J hJ).map e'.symm.toMonoidHom = (P : Subgroup L) := by
    change (projectiveRoot J hJ).map (e.symm.toMonoidHom.comp (MulAut.conj k).toMonoidHom) = _
    rw [←map_map,hkRoot]
    change ((P : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom = _
    rw [map_map,hc,map_id]
  have heP : ((center P').map (P' : Subgroup _).subtype).map e.symm.toMonoidHom =
      (center P).map (P : Subgroup L).subtype := by
    rw [map_embeddedCenter _ _ e.symm.injective]
    have hp : (P' : Subgroup _).map e.symm.toMonoidHom = (P : Subgroup L) := by
      change ((P : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom = _
      rw [map_map,hc,map_id]
    rw [hp]
  have heQ : ((center Q').map (Q' : Subgroup _).subtype).map e.symm.toMonoidHom =
      (center Q).map (Q : Subgroup L).subtype := by
    rw [map_embeddedCenter _ _ e.symm.injective]
    have hp : (Q' : Subgroup _).map e.symm.toMonoidHom = (Q : Subgroup L) := by
      change ((Q : Subgroup L).map e.toMonoidHom).map e.symm.toMonoidHom = _
      rw [map_map,hc,map_id]
    rw [hp]
  have hp : (standardPair J hJ).map (MarkedTorus.residualModelMap J e') = I.map q := by
    change (standardPair J hJ).map
      (L.subtype.comp (e.symm.toMonoidHom.comp (MulAut.conj k).toMonoidHom)) = _
    rw [←map_map,←map_map,hkPair,Subgroup.map_sup,heP,heQ,←hpair]
  have hroot : (projectiveRoot J hJ).map (MarkedTorus.residualModelMap J e') =
      (T : Subgroup H).map q ⊓ L := by
    change (projectiveRoot J hJ).map (L.subtype.comp e'.symm.toMonoidHom) = _
    rw [←map_map,hr,hP]
  have hT : (T : Subgroup H).map q ≤ normalizer
      ((projectiveRoot J hJ).map (MarkedTorus.residualModelMap J e') : Set (H ⧸ pCore 2 H)) := by
    rw [hroot]
    exact (le_inf ((T : Subgroup H).map q).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  exact MarkedTorus.exists_quotient_five_of_coordinates J hJ hcard hconj
    T M I hlocal e' hp hT

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuUnitary
