module
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.PointHyperplane
public import Theory.Representation.G2BinaryPointMovement

/-!
# Actual movement and the unitary source hyperplane

The literal automizer lifts every native linear displacement to an ambient
commutator. In the nonabelian-closure branch, F.9.3 makes the U_H image
nontrivial, so its native displacement equality yields V₃≤[V,U_H]. The
preceding hyperplane proof now has its movement premise discharged, giving
V∩Q_H=V₅ in coordinates and corank one for the actual ambient subgroups.

The same marking transports the invariant-pairing consequence: every
original actor centralizing V₃ has displacement in V₃. This is the final
linear step in the cross-displacement argument; the preceding source
plane-fusion contradiction must still establish that centralization.

The only retained source data are genuine F.9 applicability, the actual
natural module/point frame, and the earlier 13.3.17 conclusions. This module
does not assert the full exclusion Theorem 13.3.16.

Source: Aschbacher–Smith, Lemma 13.3.18, printed p.895.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open Subgroup ChapterE Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
open Atlas.G2.Natural.BinaryPointFlag
variable {G:Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Native displacements lift to the original ambient commutators through
the actual normalizer action; no involutory lift is selected. -/
theorem point_displacement_le_actual_commutator
    (V A:Subgroup G) [IsElementaryAbelian 2 V]
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) :
    subspaceCommutator (Atlas.G2.Restricted.NaturalCoordinates.action F) ⊤
      ((inducedAutomizer V A).map rho)≤pointCoordinateSubspace E ⁅V,A⁆ := by
  apply Submodule.span_le.mpr
  rintro w ⟨_,⟨a,⟨n,hnA,rfl⟩,rfl⟩,v,_,rfl⟩
  obtain ⟨v,rfl⟩:=E.surjective v
  rw [←he,←map_sub]
  apply (mem_pointCoordinateSubspace E ⁅V,A⁆ _).mpr
  simp only [toMul_sub,div_eq_mul_inv]
  change (n:G)*v.toMul.val*(n:G)⁻¹*v.toMul.val⁻¹∈⁅V,A⁆
  rw [commutator_comm]
  exact commutator_mem_commutator hnA v.toMul.prop

/-- In the nonabelian-closure branch, the actual smaller closure moves
all of the original seed, as required by the Hall–Witt step. -/
theorem seed_le_commutator_of_point_action
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    pointCoordinateSubspace E D.Vplus=seed →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    (∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) →
    ¬IsMulCommutative D.VH → D.Vplus≤⁅D.V,D.UH⁆ := by
  let :=h.elementary
  dsimp only
  intro rho E he hs hT hP hcomm hnonabelian
  let A:Subgroup (Atlas.G2.Model F):=(inducedAutomizer D.V D.UH).map rho
  let :IsElementaryAbelian 2 A:=seed_closure_model_image_elementary h rho
  have hU: D.UH≤normalizer (D.V:Set G) :=
    h.UH_le_QH.trans (h.QH_le_T.trans h.T_normalizes_V)
  have hA:A≤Atlas.G2.unipotent :=
    (map_mono (map_mono (comap_mono (h.UH_le_QH.trans h.QH_le_T)))).trans hT
  have hn:Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤normalizer (A:Set _) := by
    have hN:(D.L₁⊔(D.T:Subgroup G)).subgroupOf (normalizer (D.V:Set G))≤
        normalizer (D.UH.subgroupOf (normalizer (D.V:Set G)):Set (normalizer (D.V:Set G))) := by
      intro n hnJ
      apply mem_normalizer_iff.mpr
      intro a
      exact mem_normalizer_iff.mp
        (le_normalizer_conjugateSpanBy D.Vplus D.H (h.local_le hnJ)) a.val
    exact hP.trans ((map_mono ((map_mono hN).trans
      ((D.UH.subgroupOf (normalizer (D.V:Set G))).le_normalizer_map
        D.V.normalizerMonoidHom.rangeRestrict))).trans
      ((inducedAutomizer D.V D.UH).le_normalizer_map rho))
  have hf:Function.Injective rho := by
    intro a b hab
    apply automizerRepresentation_injective D.V
    apply LinearMap.ext
    intro v
    apply E.injective
    rw [he,he,hab]
  have hne:A≠⊥ := by
    intro hzero
    have hz:inducedAutomizer D.V D.UH=⊥ := map_injective hf (by simpa only [A,Subgroup.map_bot] using hzero)
    have hc: D.V≤centralizer (D.UH:Set G) :=
      le_centralizer_iff.mp ((inducedAutomizer_eq_bot_iff hU).mp hz)
    exact hnonabelian (closure_abelian_of_le_core h hcomm
      (h.lemma_F_9_3.1.mpr (le_inf h.V_le_H hc)))
  have hm:=normal_elementary_displacement_eq_seed A hA hn hne
  have hbound:seed≤pointCoordinateSubspace E ⁅D.V,D.UH⁆ :=
    hm ▸ point_displacement_le_actual_commutator D.V D.UH rho E he
  intro v hv
  let w:Additive D.V:=Additive.ofMul ⟨v,h.plus_le hv⟩
  have hw:E w∈seed:=hs ▸ (mem_pointCoordinateSubspace E D.Vplus w).mpr hv
  exact (mem_pointCoordinateSubspace E ⁅D.V,D.UH⁆ w).mp (hbound hw)

/-- The original core intersection has corank one, with the movement and
smaller-closure premises now discharged by the actual native action. -/
theorem source_point_hyperplane
    {D:ChapterF.Section09.Setup G} (h:D.Hypothesis) :
    let :=h.elementary
    ∀ (rho:Automizer D.V→*Atlas.G2.Model F) (E:Additive D.V≃ₗ[F]W),
    (∀a v,E (automizerRepresentation D.V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v)) →
    pointCoordinateSubspace E D.Vplus=seed →
    (inducedAutomizer D.V (D.T:Subgroup G)).map rho≤Atlas.G2.unipotent →
    Atlas.G2.BinaryParabolicPair.derivedSecondAmbient≤
      (inducedAutomizer D.V (D.L₁⊔(D.T:Subgroup G))).map rho →
    (∀g∈D.H,⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆≤
      D.V⊓D.V.map (MulAut.conj g).toMonoidHom →
      ⁅D.V,D.V.map (MulAut.conj g).toMonoidHom⁆=⊥) →
    ¬IsMulCommutative D.VH → ¬D.Vplus≤centralizer (D.QH:Set G) →
    pointCoordinateSubspace E (D.V⊓D.QH)=hyperplane ∧
      subgroupCorank D.V (D.V⊓D.QH)=1 := by
  let :=h.elementary
  dsimp only
  intro rho E he hs hT hP hcomm hnonabelian hnoncentral
  exact core_intersection_point_hyperplane h rho E he hs hT hP hcomm hnonabelian
    (seed_le_commutator_of_point_action h rho E he hs hT hP hcomm hnonabelian) hnoncentral

omit [Finite G] in
/-- The pointwise-centralizer step of the cross-displacement argument on
literal original subgroups, transported through the same natural marking. -/
theorem commutator_le_seed_of_point_centralizer
    (V B A:Subgroup G) [IsElementaryAbelian 2 V]
    (rho:Automizer V→*Atlas.G2.Model F) (E:Additive V≃ₗ[F]W)
    (he:∀a v,E (automizerRepresentation V a v)=
      Atlas.G2.Restricted.NaturalCoordinates.action F (rho a) (E v))
    (hs:pointCoordinateSubspace E B=seed)
    (hAN:A≤normalizer (V:Set G)) (hAC:A≤centralizer (B:Set G)) : ⁅V,A⁆≤B := by
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha v hv
  let n:normalizer (V:Set G):=⟨a,hAN ha⟩
  let i:Automizer V:=V.normalizerMonoidHom.rangeRestrict n
  have hfix:∀w∈seed,Atlas.G2.Restricted.NaturalCoordinates.action F (rho i) w=w := by
    intro w hw
    obtain ⟨x,rfl⟩:=E.surjective w
    have hx:(x.toMul:G)∈B := (mem_pointCoordinateSubspace E B x).mp (hs.symm ▸ hw)
    rw [←he]
    apply congrArg E
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change a*x.toMul.val*a⁻¹=x.toMul.val
    rw [←hAC ha x.toMul.val hx,mul_inv_cancel_right]
  let w:Additive V:=Additive.ofMul ⟨v,hv⟩
  have hd:=displacement_mem_seed (rho i) hfix (E w)
  have hh:E (automizerRepresentation V i w-w)∈pointCoordinateSubspace E B := by
    rw [hs,map_sub,he]
    exact hd
  have hb:((automizerRepresentation V i w-w).toMul:G)∈B :=
    (mem_pointCoordinateSubspace E B _).mp hh
  simp only [toMul_sub,div_eq_mul_inv] at hb
  exact hb

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
