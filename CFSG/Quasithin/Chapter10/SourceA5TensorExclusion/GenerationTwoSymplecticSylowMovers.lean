module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.GenerationTwoSymplecticSmallMoverKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.SourceComparison.OriginalSmallMoverSylow
public import Theory.GroupTheory.RelativeProductBound

/-!
# The original tensor edge has a unique maximum small mover

The original radical is an actual Sylow subgroup. Its faithful natural action
therefore has a unique maximum small mover, whose quotient by the literal
kernel has order64 and whose centralizer has index16. This proves the
product exclusion of MS93 (5.1) on the original geometry and identifies the
canonical subgroup used in the selected-generator argument.

The later generator selection and strict moving index remain to be proved.
Source: MS93 (5.0)--(5.6), pp.912--918; Aschbacher--Smith9.3.10, p.734.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
open Chapter3.Section02 ChapterC.MSCentralOrbit ChapterB.QuasisimpleSource
open ChapterC.RankTwo.Sp4Four ChapterC.RankTwo.Sp4Four.SourceComparison
open Theory.SpecificGroups.SymplecticFour
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  {m : SourceA5TensorModel D e} (c : m.GenerationTwoOvergroup)

/-- The original full Sylow edge has exactly one maximum small mover. -/
theorem original_sylow_maximal_mover
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      ∃ E : Subgroup (FreeAmalgam R), LocalPackage.MaximalMovers R a t = {E} ∧
        (Q R a).relIndex E = 64 ∧
        (centralizer (E : Set (FreeAmalgam R))).relIndex (U R a) = 16 := by
  intro R a t ha hat
  obtain ⟨hodd,hms⟩ := source_nonnormal_stabilizer_msInputs D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
  let q := QuotientGroup.mk' (pCore 2 c.M)
  obtain ⟨hKN,hBN,hBS,hBQ,hBC,hcard,hsq,hQne⟩ :=
    source_tensor_sp4_quotient_data D m.sylow_not_normalizes_component c.M
      (c.generated ▸ le_sup_right) (c.generated ▸ le_sup_of_le_left le_sup_left)
      c.outside c.sylow (pResidual 2 c.M) c.component_product.1
      BinaryField.four.card_eq eK c.fitting_center.1 c.component_product.2.2.2
  let := hKN
  let := hBN
  let := hBS
  let := hBQ
  obtain ⟨_,hfaith,_⟩ := source_tensor_sp4_msCentralOrbit D
    m.sylow_not_normalizes_component c.M (c.generated ▸ le_sup_right)
    (c.generated ▸ le_sup_of_le_left le_sup_left) c.outside c.sylow
    (pResidual 2 c.M) c.component_product.1 BinaryField.four.card_eq eK
    c.fitting_center.1 c.component_product.2.2.2
  have hself : centralizer (pCore 2 c.M : Set c.M) ≤ pCore 2 c.M := by
    simpa only [c.fitting_center.1] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := c.M))
  have hne : R ≠ ⊥ := fun hr => hQne (le_bot_iff.mp (hr ▸ hodd.twoCore_le))
  obtain ⟨geometry,hpos,_⟩ := c.exists_positive_even_geometry eK
  have hfixed : U R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hcore : x ∈ fixedCore R a := ⟨
      ((U_le_Z a).trans (geometry.omega_bound a ha
        (by
          rw [geometry.distance_constant a ha]
          change 0 < geometry.b R
          omega)) |>.trans (omegaCenter_le _)) hx.1,hx.2⟩
    rwa [c.original_fixedCore_eq_bot a ha] at hcore
  have ht : color R t = true := by
    have h := adjacent_color_ne R hat
    rw [ha] at h
    cases he : color R t <;> simp_all
  obtain ⟨P,hP⟩ := c.sylow
  have hPR : (P : Subgroup c.M) = R := by
    apply Subgroup.map_injective c.M.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le (c.generated ▸ le_sup_right)]
  obtain ⟨i,hi,hir,hiR,_,_⟩ := LocalPackage.edge_coordinates R hodd.isPGroup hodd.twoCore_le ha hat
  let iS := i.codRestrict (stabilizer R a) (fun x => hir ▸ (show i x ∈ i.range from ⟨x,rfl⟩))
  have hiS : Function.Surjective iS := by
    intro x
    obtain ⟨y,hy⟩ := (show x.val ∈ i.range from hir.symm ▸ x.property)
    exact ⟨y,Subtype.ext hy⟩
  have hSylow : ∃ S : Sylow 2 (stabilizer R a),
      (S : Subgroup _) = (Q R t).subgroupOf (stabilizer R a) := by
    refine ⟨P.mapSurjective (f := iS) hiS,?_⟩
    apply Subgroup.map_injective (stabilizer R a).subtype_injective
    rw [Sylow.coe_mapSurjective,Subgroup.map_map,hPR,
      map_subgroupOf_eq_of_le (show Q R t ≤ stabilizer R a from
        fun _ hx => hx.2 a (adjacent_symm R hat))]
    exact hiR
  exact original_sylow_small_mover_unique R hms hodd.isPGroup hne hodd.twoCore_le
    hself hfaith q (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)
    hcard hBC hsq ha hfixed (Q R t)
    (fun _ hx => hx.2 a (adjacent_symm R hat)) (Q_le_adjacent_h R ht hat) hSylow

/-- Exact indices of the canonical subgroup used in the original selected generation. -/
theorem original_small_mover_join_indices
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      LocalPackage.MaximalMovers R a t = {LocalPackage.J R a t} ∧
      (Q R a).relIndex (LocalPackage.J R a t) = 64 ∧
      (centralizer (LocalPackage.J R a t : Set (FreeAmalgam R))).relIndex (U R a) = 16 := by
  intro R a t ha hat
  obtain ⟨E,hE,hi,hmove⟩ := c.original_sylow_maximal_mover eK ha hat
  have hJ : LocalPackage.J R a t = E := by
    change sSup (LocalPackage.MaximalMovers R a t) = E
    rw [hE,sSup_singleton]
  rw [hJ]
  exact ⟨hE,hi,hmove⟩
open scoped Pointwise in
/-- The original full-Sylow instance of MS93 (5.1): two order-four
quotient images cannot cover its order64 maximum mover. -/
theorem original_small_mover_not_subset_product
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ {a t : Vertex R}, color R a = false → Adjacent R a t →
      ∀ E A : Subgroup (FreeAmalgam R), E ≤ Q R t → A ≤ Q R t →
        (Q R a).relIndex E = 4 → (Q R a).relIndex A = 4 →
        ¬ (LocalPackage.J R a t : Set (FreeAmalgam R)) ⊆ (E : Set _) * (A : Set _) := by
  intro R a t ha hat E A hET hAT hE hA hprod
  let S := stabilizer R a
  let := finite_stabilizer R a
  let N := (Q R a).subgroupOf S
  let : N.Normal := normal_subgroupOf_of_le_normalizer (Q_normalized R a)
  have hTS : Q R t ≤ S := fun _ hx => hx.2 a (adjacent_symm R hat)
  have hES := hET.trans hTS
  have hAS := hAT.trans hTS
  have hJS := (LocalPackage.J_le_radical R a t).trans hTS
  have hi (K : Subgroup (FreeAmalgam R)) (hKS : K ≤ S) :
      N.relIndex (K.subgroupOf S) = (Q R a).relIndex K := by
    rw [←relIndex_map_map_of_injective _ _ S.subtype_injective,
      map_subgroupOf_eq_of_le (show Q R a ≤ S from fun _ hx => hx.1),
      map_subgroupOf_eq_of_le hKS]
  have hp : ((LocalPackage.J R a t).subgroupOf S : Set S) ⊆
      (E.subgroupOf S : Set S) * (A.subgroupOf S : Set S) := by
    intro x hx
    obtain ⟨u,hu,v,hv,huv⟩ := hprod hx
    exact ⟨⟨u,hES hu⟩,hu,⟨v,hAS hv⟩,hv,Subtype.ext huv⟩
  have hh := relIndex_le_mul_of_subset_product N ((LocalPackage.J R a t).subgroupOf S)
    (E.subgroupOf S) (A.subgroupOf S) hp
  rw [hi _ hJS,hi _ hES,hi _ hAS,hE,hA] at hh
  have hj := (c.original_small_mover_join_indices eK ha hat).2.1
  change (Q R a).relIndex (LocalPackage.J R a t) = 64 at hj
  rw [hj] at hh
  omega

/-- Any selected maximum is the same canonical original generator, so its
normalization is already available in the backward-path application. -/
theorem original_maximal_mover_backward_path
    (eK : (pResidual 2 c.M ⧸ pCore 2 (pResidual 2 c.M)) ≃* Sp BinaryField.four.Carrier) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf c.M)
    ∀ (geometry : Geometry R), 4 < geometry.b R →
      ∀ {a z d t : Vertex R} (path : CriticalPath R geometry a z),
      Adjacent R a t → Adjacent R d t →
      ¬ Z R z ≤ normalizer ((Z R d ⊔ Z R a : Subgroup (FreeAmalgam R)) : Set _) →
      ∀ E ∈ LocalPackage.MaximalMovers R d t,
      Ltilde R a ≤ E ⊔ Z R z →
      4 < (CFSG.Quasithin.ChapterC.BinaryMS.MS93.B R a (geometry.Z_normal a)).relIndex (U R d) →
      (∃ back : CriticalPath R geometry d (path.walk.getVert (path.walk.length-2)),
        back.walk.getVert 1=t ∧
        ∀ i ≤ path.walk.length-2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
      ¬ V R a ≤ Q R (path.walk.getVert (path.walk.length-2)) := by
  intro R geometry hb a z d t path hat hdt hbad E hE hgen hmove
  have hd : color R d = false := by
    have h := adjacent_color_ne R hat
    have h' := adjacent_color_ne R hdt
    rw [path.start_color] at h
    cases he : color R d <;> cases ht : color R t <;> simp_all
  rw [(c.original_small_mover_join_indices eK hd hdt).1] at hE
  have he := Set.mem_singleton_iff.mp hE
  rw [he] at hgen
  exact c.original_small_movers_backward_path eK geometry hb path hat hdt hbad hgen hmove

end CFSG.Quasithin.Chapter10.SourceA5TensorModel.GenerationTwoOvergroup
