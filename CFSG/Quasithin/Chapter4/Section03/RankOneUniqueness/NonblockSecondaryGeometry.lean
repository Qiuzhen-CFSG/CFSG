module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockMSCore
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondaryAction
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.HigherFieldResiduals
public import Theory.GroupTheory.SolvableResidual.Transport
/-!
# The literal nonblock root centralizer and its secondary quotient

The full source root lies in Z(Q). The original intersection H∩N_G(Z_S)
normalizes K₂=C_K(Z_S)^∞, and S normalizes K₂. Independently of any
secondary-component construction, Q≤R₂≤S and R₂≤N_G(Z_S).

A common natural-module marking carrying the root to the first coordinate
line identifies the actual root centralizer with the preimage of the vector
stabilizer in SL₃. Restricting the original quotient map to the solvable
residual gives a surjection with two-group kernel. Its quotient by the
intrinsic two-core is therefore SL₂, with a formula on representatives.
If the original L-image contains the line local, the two local images
generate SL₃. The original two-core normalizes both lifts; perfectness of K
then removes the apparent two-core supplement and proves ⟨L,K₂⟩=K.

The final application supplies the literal rank-one model, strict component
containment and nontrivial R₂ quotient action. The natural root coordinates,
line-parabolic placement, component selection and preceding 4.3.14 bounds
remain explicit source inputs, owned by
`qt-d-1222-rankone-uniqueness-nonblock`. No MSData or SecondaryData witness
is asserted here.
Source: Aschbacher--Smith, original 4.3.10--15, printed pp.617--618;
the matrix vector/covector stabilizers are the local groups of A.3.14.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L} {n : ℕ}

theorem MSData.root_le_center (d : MSData c n) : root c ≤ U c := by
  apply inf_le_left.trans
  rw [←d.fullModule]
  exact le_normalizer_iff_commutator_le_left.mp (c.le_component.trans d.natural.2.1)

theorem MSData.core_centralizes_root (d : MSData c n) :
    Q c ≤ Subgroup.centralizer (root c : Set G) := by
  intro q hq z hz
  obtain ⟨u,hu,rfl⟩ := d.root_le_center hz
  exact (congrArg Subtype.val (mem_center_iff.mp hu ⟨q,hq⟩)).symm

theorem secondary_le_original : secondary c ≤ K c :=
  (map_subtype_le _).trans inf_le_left

theorem secondary_centralizes_root : secondary c ≤ centralizer (root c : Set G) :=
  (map_subtype_le _).trans inf_le_right

theorem original_root_normalizer_normalizes_secondary :
    c.H ⊓ rootNormalizer c ≤ normalizer (secondary c : Set G) := by
  apply le_trans _ (normalizer_le_normalizer_characteristic_image
    (K c ⊓ centralizer (root c : Set G))
    (solvableResidual (K c ⊓ centralizer (root c : Set G) : Subgroup G)))
  apply le_trans _ inf_normalizer_le_normalizer_inf
  exact le_inf (inf_le_left.trans c.normalizer_component.le)
    (inf_le_right.trans (normalizer_le_normalizer_centralizer (root c)))

theorem sylow_normalizes_secondary (D : Chapter12.Section02.ChosenModule T L V) :
    S c ≤ normalizer (secondary c : Set G) :=
  (le_inf inf_le_right (inf_le_left.trans (root_normalized c D))).trans
    original_root_normalizer_normalizes_secondary

theorem radical_le_root_normalizer (D : Chapter12.Section02.ChosenModule T L V) :
    R₂ c ≤ rootNormalizer c :=
  (pCoreIn_le 2 _).trans (sup_le
    (secondary_centralizes_root.trans (Subgroup.centralizer_le_normalizer _))
    (inf_le_left.trans (root_normalized c D)))

theorem core_le_radical [Finite G] (c : SourceConfiguration T L) : Q c ≤ R₂ c := by
  have hQ : Q c ≤ secondary c ⊔ S c := (core_le_sylow c).trans le_sup_right
  have hn : secondary c ⊔ S c ≤ normalizer (Q c : Set G) :=
    (sup_le (secondary_le_original.trans (map_subtype_le _)) inf_le_right).trans
      (core_normalized c)
  have hp : IsPGroup 2 (Q c) :=
    (T.isPGroup'.to_le (show Q c ≤ (T : Subgroup G) from (core_le_sylow c).trans inf_le_left))
  exact le_pCoreIn_of_normalizes hp hQ hn


theorem secondary_normal_in_original_root_normalizer :
    ((secondary c).subgroupOf (c.H ⊓ rootNormalizer c)).Normal := by
  have hle : secondary c ≤ c.H ⊓ rootNormalizer c :=
    le_inf (secondary_le_original.trans (map_subtype_le _))
      (secondary_centralizes_root.trans (Subgroup.centralizer_le_normalizer _))
  exact (normal_subgroupOf_iff_le_normalizer hle).mpr
    original_root_normalizer_normalizes_secondary


theorem radical_le_sylow (c : SourceConfiguration T L) : R₂ c ≤ S c := by
  have hRS : S c ≤ normalizer (R₂ c : Set G) :=
    (le_sup_right : S c ≤ secondary c ⊔ S c).trans
      ((secondary c ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (secondary c ⊔ S c)
          (pCore 2 (secondary c ⊔ S c : Subgroup G))))
  have hp : IsPGroup 2 (R₂ c ⊔ S c : Subgroup G) :=
    (isPGroup_pCoreIn 2 (secondary c ⊔ S c)).to_sup_of_normal_left'
      (T.isPGroup'.to_le inf_le_left) hRS
  have hH : R₂ c ⊔ S c ≤ c.H := sup_le
    ((pCoreIn_le 2 _).trans (sup_le
      (secondary_le_original.trans (map_subtype_le _)) inf_le_right)) inf_le_right
  obtain ⟨P,hP⟩ := c.sylow
  have he : (R₂ c ⊔ S c).subgroupOf c.H = (P : Subgroup c.H) :=
    P.is_maximal' (hp.comap_subtype) (by
      intro x hx
      exact (le_sup_right : S c ≤ R₂ c ⊔ S c) (hP.le (mem_map_of_mem _ hx)))
  have hm := congrArg (map c.H.subtype) he
  rw [map_subgroupOf_eq_of_le hH,hP] at hm
  exact le_sup_left.trans_eq hm

open scoped MatrixGroups
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Matrix.PSL3.LinearThree
noncomputable section

/-- A coordinate marking of the original root in the common natural module.
Only the root line and its action are marked; no secondary quotient is assumed. -/
structure RootCoordinates (d : MSData c n) where
  coordinates : U c ≃* Multiplicative (Fin 3 → d.field.Carrier)
  compatible : ∀ (k : K c) (u u' : U c), (u' : G) = k * (u : G) * (k : G)⁻¹ →
    (coordinates u').toAdd =
      Representation.specialLinearNatural 3 (linearThreeActor d.model k) (coordinates u).toAdd
  root_coordinates : ∀ u : U c, (u : G) ∈ root c ↔
    ∃ a : d.field.Carrier, (coordinates u).toAdd = a • (![1,0,0] : Fin 3 → d.field.Carrier)

abbrev rootCentralizer (c : SourceConfiguration T L) : Subgroup G :=
  K c ⊓ Subgroup.centralizer (root c : Set G)

namespace RootCoordinates
variable {d : MSData c n} (m : RootCoordinates d)

private def conjugate (_m : RootCoordinates d) (k : K c) (u : U c) : U c :=
  ⟨k * (u : G) * (k : G)⁻¹,
    (mem_normalizer_iff.mp (d.natural.2.1 k.property) u).mp u.property⟩

include m

private theorem coordinates_conjugate (k : K c) (u : U c) :
    (m.coordinates (m.conjugate k u)).toAdd =
      Representation.specialLinearNatural 3 (linearThreeActor d.model k) (m.coordinates u).toAdd :=
  m.compatible k u (m.conjugate k u) rfl

/-- The actual root centralizer is the preimage of the vector stabilizer. -/
theorem centralizer_iff (k : K c) :
    (k : G) ∈ Subgroup.centralizer (root c : Set G) ↔
      linearThreeActor d.model k ∈ pointLocalSL d.field.Carrier := by
  let v : Fin 3 → d.field.Carrier := ![1,0,0]
  constructor
  · intro hk
    let u := m.coordinates.symm (Multiplicative.ofAdd v)
    have hu : (u : G) ∈ root c := (m.root_coordinates u).mpr ⟨1, by simp [u,v]⟩
    have he : m.conjugate k u = u := by
      apply Subtype.ext
      change k * (u : G) * (k : G)⁻¹ = (u : G)
      rw [←mem_centralizer_iff.mp hk _ hu, mul_inv_cancel_right]
    have hh := m.coordinates_conjugate k u
    rw [he] at hh
    change (linearThreeActor d.model k).val.mulVec v = v
    simpa only [u, MulEquiv.apply_symm_apply, toAdd_ofAdd, Representation.specialLinearNatural_apply,
      Matrix.SpecialLinearGroup.smul_def] using hh.symm
  · intro hk z hz
    let u : U c := ⟨z,d.root_le_center hz⟩
    obtain ⟨a,ha⟩ := (m.root_coordinates u).mp hz
    have hf : Representation.specialLinearNatural 3 (linearThreeActor d.model k) v = v := hk
    have he : m.conjugate k u = u := by
      apply m.coordinates.injective
      apply Multiplicative.toAdd.injective
      rw [m.coordinates_conjugate, ha, map_smul, hf]
    have he' := congrArg Subtype.val he
    change (k : G) * z * (k : G)⁻¹ = z at he'
    exact (mul_inv_eq_iff_eq_mul.mp he').symm

/-- The original quotient map, restricted and corestricted at the root centralizer. -/
def centralizerProjection : rootCentralizer c →* pointLocalSL d.field.Carrier :=
  ((linearThreeActor d.model).comp (inclusion (show rootCentralizer c ≤ K c from inf_le_left))).codRestrict
    (pointLocalSL d.field.Carrier) (fun x => (m.centralizer_iff ⟨x,x.property.1⟩).mp x.property.2)

@[simp] theorem centralizerProjection_apply (x : rootCentralizer c) :
    (m.centralizerProjection x : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) =
      linearThreeActor d.model ⟨x,x.property.1⟩ := rfl

theorem centralizerProjection_surjective : Function.Surjective m.centralizerProjection := by
  intro a
  obtain ⟨k,hk⟩ := (d.model.surjective.comp (QuotientGroup.mk'_surjective _)) (a : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier)
  change linearThreeActor d.model k = a at hk
  refine ⟨⟨k,k.property,(m.centralizer_iff k).mpr (hk.symm ▸ a.property)⟩,?_⟩
  exact Subtype.ext hk

/-- Its kernel is a subgroup of the literal O₂(K), not merely solvable. -/
theorem centralizerProjection_kernel : IsPGroup 2 m.centralizerProjection.ker := by
  let i : m.centralizerProjection.ker →* pCore 2 (K c) := {
    toFun := fun x => ⟨⟨x.val.val,x.val.property.1⟩, by
      apply (QuotientGroup.eq_one_iff _).mp
      apply d.model.injective
      have hx := congrArg Subtype.val x.property
      change linearThreeActor d.model ⟨x.val.val,x.val.property.1⟩ = 1 at hx
      simpa only [linearThreeActor,MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,
        MonoidHom.coe_coe,QuotientGroup.mk'_apply,map_one] using hx⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  apply (pCore_isPGroup (p := 2) (G := K c)).of_injective i
  intro x y he
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : pCore 2 (K c) => ((z : K c) : G)) he

/-- The original perfect secondary subgroup, through its actual inclusion. -/
def secondaryProjection : secondary c →* pointLocalSL d.field.Carrier :=
  m.centralizerProjection.comp (inclusion (map_subtype_le _))

@[simp] theorem secondaryProjection_apply (x : secondary c) :
    (m.secondaryProjection x : Matrix.SpecialLinearGroup (Fin 3) d.field.Carrier) =
      linearThreeActor d.model ⟨x,secondary_le_original x.property⟩ := rfl

theorem secondaryProjection_surjective [Finite G] (hn : 1 < n) :
    Function.Surjective m.secondaryProjection := by
  have hF : 4 ≤ Nat.card d.field.Carrier := by
    rw [d.field.card_eq,d.degree_eq]
    exact (show 4 = 2 ^ 2 from rfl).trans_le (Nat.pow_le_pow_right (by decide) hn)
  let := pointLocalSL_isPerfect d.field.Carrier hF
  have he := map_solvableResidual_eq m.centralizerProjection m.centralizerProjection_surjective
  rw [solvableResidual_eq_top (G := pointLocalSL d.field.Carrier)] at he
  intro a
  obtain ⟨x,hx,hxa⟩ := he.ge (mem_top a)
  exact ⟨⟨x,mem_map_of_mem _ hx⟩,hxa⟩

theorem secondaryProjection_kernel : IsPGroup 2 m.secondaryProjection.ker := by
  change IsPGroup 2 (m.centralizerProjection.comp (inclusion (map_subtype_le _))).ker
  rw [←MonoidHom.comap_ker]
  exact m.centralizerProjection_kernel.comap_of_injective _ (inclusion_injective _)

/-- The secondary two-core quotient is the genuine rank-one matrix group. -/
def secondaryCoreEquiv [Finite G] (hn : 1 < n) :
    (secondary c ⧸ pCore 2 (secondary c)) ≃*
      Matrix.SpecialLinearGroup (Fin 2) d.field.Carrier :=
  (m.secondaryProjection.pCoreQuotientEquiv (m.secondaryProjection_surjective hn)
    m.secondaryProjection_kernel).trans (pointLocalSLCoreQuotientEquiv d.field.Carrier)

/-- This quotient identification retains the original root-centralizer map. -/
theorem secondaryCoreEquiv_mk [Finite G] (hn : 1 < n) (x : secondary c) :
    m.secondaryCoreEquiv hn (QuotientGroup.mk' (pCore 2 (secondary c)) x) =
      pointLocalSLCoreQuotientEquiv d.field.Carrier
        (QuotientGroup.mk' (pCore 2 (pointLocalSL d.field.Carrier)) (m.secondaryProjection x)) := rfl


/-- The actual quotient is the source PSL₂(2ⁿ) model, with its literal two-core. -/
theorem secondary_model [Finite G] (hn : 1 < n) :
    ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n) := by
  exact ⟨d.field.Carrier, inferInstance, inferInstance,
    d.field.card_eq.trans (congrArg (2 ^ ·) d.degree_eq),
    ⟨(m.secondaryCoreEquiv hn).trans (Theory.PSL2.sl2QuotientEquiv d.field.Carrier)⟩⟩

omit m in
private theorem intrinsic_core_le_sylow [Finite G] : (K c).pCoreIn 2 ≤ S c := by
  rw [←map_pCoreIn_of_injective 2 c.K c.H.subtype c.H.subtype_injective]
  exact ((map_mono (pCoreIn_le_of_subnormal 2 c.component.subnormal)).trans
    c.c28.ambient_core_le_radical).trans (c.core_sylow.le.trans inf_le_left)

/-- The two marked local images generate the original K. The original two-core
normalizes both local factors, so its apparent supplement disappears by
perfectness. No containment O₂(K)≤L is assumed. -/
theorem original_sup_secondary [Finite G] (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : lineLocalSL d.field.Carrier ≤
      (L.subgroupOf (K c)).map (linearThreeActor d.model)) :
    L ⊔ secondary c = K c := by
  let A := L ⊔ secondary c
  have hAK : A ≤ K c := sup_le c.le_component secondary_le_original
  let A₀ := A.subgroupOf (K c)
  let f := linearThreeActor d.model
  have hk : f.ker = pCore 2 (K c) := by
    dsimp only [f,linearThreeActor]
    rw [MonoidHom.ker_comp_of_injective _ _ d.model.injective,QuotientGroup.ker_mk']
  have hsec : pointLocalSL d.field.Carrier ≤ ((secondary c).subgroupOf (K c)).map f := by
    intro a ha
    obtain ⟨x,hx⟩ := m.secondaryProjection_surjective hn ⟨a,ha⟩
    exact ⟨⟨x,secondary_le_original x.property⟩,x.property,congrArg Subtype.val hx⟩
  have him : A₀.map f = ⊤ := by
    apply top_unique
    rw [←localsSL_sup_eq_top d.field.Carrier]
    exact sup_le (hsec.trans (map_mono (comap_mono le_sup_right)))
      (hL.trans (map_mono (comap_mono le_sup_left)))
  have hs : A₀ ⊔ pCore 2 (K c) = ⊤ := by
    rw [←hk,←comap_map_eq,him,comap_top]
  have hsG : A ⊔ (K c).pCoreIn 2 = K c := by
    have hh := congrArg (map (K c).subtype) hs
    simpa only [A₀,pCoreIn,Subgroup.map_sup,map_subgroupOf_eq_of_le hAK,
      ←MonoidHom.range_eq_map,range_subtype] using hh
  have hNL : (K c).pCoreIn 2 ≤ normalizer (L : Set G) :=
    intrinsic_core_le_sylow.trans (inf_le_left.trans D.sylow_normalizes_component)
  have hNr : (K c).pCoreIn 2 ≤ rootNormalizer c := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    rintro x ⟨k,hkcore,rfl⟩
    apply (m.centralizer_iff k).mpr
    have he : f k = 1 := by change k ∈ f.ker; rwa [hk]
    rw [show linearThreeActor d.model k = 1 from he]
    exact (pointLocalSL d.field.Carrier).one_mem
  have hNs : (K c).pCoreIn 2 ≤ normalizer (secondary c : Set G) :=
    (le_inf ((pCoreIn_le 2 _).trans (map_subtype_le _)) hNr).trans
      original_root_normalizer_normalizes_secondary
  have hNA : (K c).pCoreIn 2 ≤ normalizer (A : Set G) :=
    (le_inf hNL hNs).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hnorm : K c ≤ normalizer (A : Set G) := by
    rw [←hsG]
    exact sup_le A.le_normalizer hNA
  let : A₀.Normal := normal_subgroupOf_of_le_normalizer hnorm
  let : Group.IsPerfect c.K := c.component.perfect
  let : Group.IsPerfect (K c) := Group.IsPerfect.map c.H.subtype
  have hp := isPGroup_quotient_of_sup_eq_top A₀ (pCore 2 (K c)) pCore_isPGroup hs
  have hz : Subsingleton (K c ⧸ A₀) := by
    by_contra! hh
    exact Group.IsPerfect.not_isNilpotent (K c ⧸ A₀) hp.isNilpotent
  apply le_antisymm hAK
  intro k hk
  exact (QuotientGroup.eq_one_iff (N := A₀) ⟨k,hk⟩).mp (Subsingleton.elim _ _)


/-- Literal application to 4.3.13--15. The root coordinates and the original
line-parabolic marking discharge generation, the rank-one quotient and the
radical's inclusion in the root normalizer. Component selection and the
4.3.14 normalizer/core bounds remain with this source assembly owner. -/
theorem strict_component_and_action [Finite G] (hn : 1 < n)
    (D : Chapter12.Section02.ChosenModule T L V)
    (hL : lineLocalSL d.field.Carrier ≤
      (L.subgroupOf (K c)).map (linearThreeActor d.model))
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ normalizer (secondary c : Set G)) :
    ClassicalGroup.IsPSL (secondary c ⧸ pCore 2 (secondary c)) 2 (2 ^ n) ∧
    secondary c < B.map (rootNormalizer c).subtype ∧
    letI := hBn
    ((R₂ c).subgroupOf (rootNormalizer c)).map
      (normalQuotientAction B (pCore 2 B)) ≠ ⊥ := by
  have hgen := m.original_sup_secondary hn D hL
  refine ⟨m.secondary_model hn,
    secondary_lt_component_of_generation D hgen B hBn hsec, ?_⟩
  exact secondary_radical_action_ne_bot D hgen B hB hBn hsec hcore
    (radical_le_root_normalizer D) hnorm

end RootCoordinates
end

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
