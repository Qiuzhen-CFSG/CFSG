module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometrySieve
public import Theory.GroupTheory.SymmetricNormalQuotients
public import Mathlib.GroupTheory.NoncommPiCoprod

/-!
# The full product of actual transvection factors

A classified transvection closure has no center, and every proper normal
quotient of its model is a two-group. Projecting a second such normal closure
onto its direct factors, triviality of the ambient two-core forces it into
one coordinate. Applying this in both directions proves that two closures
are equal or centralize each other. The distinct closures of the generators
are consequently independent, and their multiplication map identifies their
full product with the original action image.

The rank-one generated FF action supplies every required factor without
extra model assumptions. The component sieve retains the actual marked
S₃, L₃(2), and S₅ actions on their displacement spaces. Each nonsolvable
factor's residual lifts as the residual of its literal preimage under a
central covering map, with the ambient inclusion and cubic normalization
retained. The companion Assembly module applies this to the original W/Z_S.

Source: Aschbacher–Smith, 6.1.19, pp.674–675, using G.6.4, pp.345–346.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterG.Section06
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
namespace NaturalFactorProduct

private theorem normal_quotient_two_of_equiv {H E : Type*} [Group H] [Group E]
    (e : H ≃* E)
    (hE : ∀ (N : Subgroup E) [N.Normal], N ≠ ⊥ → IsPGroup 2 (E ⧸ N))
    (N : Subgroup H) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (H ⧸ N) := by
  let M := N.map e.toMonoidHom
  let : M.Normal := (inferInstance : N.Normal).map _ e.surjective
  have hM : M ≠ ⊥ := by
    intro hm
    apply hn
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    simpa only [Subgroup.map_bot] using hm
  exact (hE M hM).of_equiv (QuotientGroup.congr N M e rfl).symm

private theorem model_normal_quotient_two
    {B V : Type*} [Group B] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) B V} {K : Subgroup B} {W : Submodule (ZMod 2) V}
    (hm : FactorModel ρ K W)
    (N : Subgroup K) [N.Normal] (hn : N ≠ ⊥) : IsPGroup 2 (K ⧸ N) := by
  rcases hm with ⟨m,hlo,_,e,_,_⟩ | ⟨m,hlo,_,e,_,_⟩ | ⟨m,hm,e,_,_⟩
  · by_cases h2 : m = 2
    · subst m
      let E := e.trans ((BinaryLinear.OuterCyclic.slEquivLinear 2).symm.trans
        (Classical.choice SLTwoPermThree.sl2Two_equiv_perm_three))
      exact normal_quotient_two_of_equiv E symmetric_three_normal_quotient_two N hn
    · let E := e.trans (BinaryLinear.OuterCyclic.projectiveEquivLinear (by omega : 0 < m)).symm
      let : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin m) (ZMod 2)) :=
        Atlas.psl_simple_high_rank m (by omega)
      let : IsSimpleGroup K := E.isSimpleGroup
      exact simple_normal_quotient_two N hn
  · exact normal_quotient_two_of_equiv e (symmetric_normal_quotient_two hlo) N hn
  · exact normal_quotient_two_of_equiv e (symmetric_normal_quotient_two (by omega)) N hn

private theorem normal_coordinate
    {H A B : Type*} [Group H] [Group A] [Group B]
    (hH : ∀ (N : Subgroup H) [N.Normal], N ≠ ⊥ → IsPGroup 2 (H ⧸ N))
    (hz : center H = ⊥) (hA : pCore 2 A = ⊥) (hB : pCore 2 B = ⊥)
    (f : H →* A × B) [f.range.Normal] :
    (∀ h, (f h).2 = 1) ∨ (∀ h, (f h).1 = 1) := by
  let p := (MonoidHom.fst A B).comp f
  let q := (MonoidHom.snd A B).comp f
  let : p.range.Normal := by
    rw [MonoidHom.range_comp]
    exact (inferInstance : f.range.Normal).map _ (fun a => ⟨(a,1),rfl⟩)
  let : q.range.Normal := by
    rw [MonoidHom.range_comp]
    exact (inferInstance : f.range.Normal).map _ (fun b => ⟨(1,b),rfl⟩)
  rcases normal_hom_injective_or_trivial hH hA p with hp | hp
  · left
    have hc (h : H) : (f h).2 ∈ center B := by
      apply mem_center_iff.mpr
      intro b
      obtain ⟨k,hk⟩ := (inferInstance : f.range.Normal).conj_mem (f h) ⟨h,rfl⟩ (1,b)
      have he : k = h := hp (by
        change (f k).1 = (f h).1
        simpa using congrArg Prod.fst hk)
      subst k
      exact mul_inv_eq_iff_eq_mul.mp (congrArg Prod.snd hk).symm
    rcases normal_hom_injective_or_trivial hH hB q with hq | hq
    · intro h
      have hh : h ∈ center H := mem_center_iff.mpr fun k => hq (by
        rw [map_mul,map_mul]
        exact mem_center_iff.mp (hc h) (q k))
      rw [show h = 1 from hz.le hh,map_one]
      rfl
    · intro h
      exact congrArg (fun q : H →* B => q h) hq
  · right
    intro h
    exact congrArg (fun p : H →* A => p h) hp

universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

omit [Finite G] in
private theorem factor_center {t : G} (d : TransvectionFactorModel ρ t) :
    center (normalClosure ({t} : Set G)) = ⊥ := by
  apply (eq_bot_iff_forall _).mpr
  intro x hx
  apply Subtype.ext
  exact d.disjoint.le_bot ⟨x.property,mem_centralizer_iff.mpr fun y hy =>
    congrArg Subtype.val (mem_center_iff.mp hx ⟨y,hy⟩)⟩

private theorem factor_le_or_centralizer {t s : G}
    (dt : TransvectionFactorModel ρ t) (ds : TransvectionFactorModel ρ s)
    (hcore : pCore 2 G = ⊥) :
    normalClosure ({s} : Set G) ≤ normalClosure ({t} : Set G) ∨
    normalClosure ({s} : Set G) ≤ centralizer (normalClosure ({t} : Set G) : Set G) := by
  let K := normalClosure ({t} : Set G)
  let C := centralizer (K : Set G)
  let H := normalClosure ({s} : Set G)
  let e := dt.productEquiv
  let f := e.symm.toMonoidHom.comp H.subtype
  let : f.range.Normal := by
    rw [MonoidHom.range_comp,range_subtype]
    exact Normal.map inferInstance _ e.symm.surjective
  have hK : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal,hcore]
    exact (MonoidHom.ker_eq_bot_iff K.subtype).mpr K.subtype_injective
  have hC : pCore 2 C = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : C.Normal).isSubnormal,hcore]
    exact (MonoidHom.ker_eq_bot_iff C.subtype).mpr C.subtype_injective
  rcases normal_coordinate (model_normal_quotient_two ds.model) (factor_center ds) hK hC f
    with hc | hk
  · left
    intro x hx
    have he := e.apply_symm_apply x
    change e ((f ⟨x,hx⟩).1,(f ⟨x,hx⟩).2) = x at he
    rw [hc,dt.productEquiv_apply] at he
    simp only [OneMemClass.coe_one,mul_one] at he
    exact he ▸ (f ⟨x,hx⟩).1.property
  · right
    intro x hx
    have he := e.apply_symm_apply x
    change e ((f ⟨x,hx⟩).1,(f ⟨x,hx⟩).2) = x at he
    rw [hk,dt.productEquiv_apply] at he
    simp only [OneMemClass.coe_one,one_mul] at he
    exact he ▸ (f ⟨x,hx⟩).2.property

theorem factors_eq_or_centralize {t s : G}
    (dt : TransvectionFactorModel ρ t) (ds : TransvectionFactorModel ρ s)
    (hcore : pCore 2 G = ⊥) (hs : s ≠ 1) :
    normalClosure ({s} : Set G) = normalClosure ({t} : Set G) ∨
    normalClosure ({s} : Set G) ≤ centralizer (normalClosure ({t} : Set G) : Set G) := by
  rcases factor_le_or_centralizer dt ds hcore with hst | hc
  · rcases factor_le_or_centralizer ds dt hcore with hts | hc
    · exact Or.inl (le_antisymm hst hts)
    · have hsK := subset_normalClosure (Set.mem_singleton s)
      exact (hs (ds.disjoint.le_bot ⟨hsK,hc (hst hsK)⟩)).elim
  · exact Or.inr hc

end NaturalFactorProduct
universe v

/-- A finite family of actual transvection closures giving the full group.
The independence and product map refer to their original inclusions. -/
structure TransvectionProductModel
    {G V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) where
  factors : Finset (Subgroup G)
  marked : ∀ K ∈ factors, ∃ t : G, t ≠ 1 ∧ K = normalClosure ({t} : Set G) ∧
    Nonempty (TransvectionFactorModel ρ t)
  commute : Pairwise fun K H : {K // K ∈ factors} =>
    ∀ x y : G, x ∈ K.val → y ∈ H.val → Commute x y
  independent : iSupIndep (fun K : {K // K ∈ factors} => K.val)
  join_eq : (⨆ K : {K // K ∈ factors}, K.val) = ⊤

namespace TransvectionProductModel
variable {G V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V}

/-- Multiplication of the literal factors is an isomorphism onto the whole group. -/
@[expose] def productEquiv (d : TransvectionProductModel ρ) :
    (∀ K : {K // K ∈ d.factors}, K.val) ≃* G := by
  classical
  let f := Subgroup.noncommPiCoprod d.commute
  exact MulEquiv.ofBijective f
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep d.independent,
      MonoidHom.range_eq_top.mp (Subgroup.noncommPiCoprod_range.trans d.join_eq)⟩

theorem productEquiv_single (d : TransvectionProductModel ρ)
    [DecidableEq {K // K ∈ d.factors}]
    (K : {K // K ∈ d.factors}) (x : K.val) :
    d.productEquiv (Function.update 1 K x) = (x : G) := by
  classical
  exact Subgroup.noncommPiCoprod_mulSingle (hcomm := d.commute) K x

end TransvectionProductModel

open NaturalFactorProduct in
/-- Actual classified normal closures of generators assemble into the whole
group, with pairwise commuting and independent literal factors. -/
theorem transvection_product_of_generated
    {G V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (S : Set G) (hgen : closure S = ⊤)
    (hcore : pCore 2 G = ⊥)
    (hfac : ∀ t ∈ S, t ≠ 1 → Nonempty (TransvectionFactorModel ρ t)) :
    Nonempty (TransvectionProductModel ρ) := by
  classical
  let := Fintype.ofFinite (Subgroup G)
  let F : Finset (Subgroup G) :=
    {K : Subgroup G | ∃ t ∈ S, t ≠ 1 ∧ K = normalClosure ({t} : Set G)}.toFinset
  have hmarked : ∀ K ∈ F, ∃ t : G, t ≠ 1 ∧ K = normalClosure ({t} : Set G) ∧
      Nonempty (TransvectionFactorModel ρ t) := by
    intro K hK
    obtain ⟨t,ht,ht1,rfl⟩ := Set.mem_toFinset.mp hK
    exact ⟨t,ht1,rfl,hfac t ht ht1⟩
  have hc : ∀ K H : {K // K ∈ F}, K ≠ H → H.val ≤ centralizer (K.val : Set G) := by
    intro K H hne
    obtain ⟨t,_,hKt,⟨dt⟩⟩ := hmarked K K.property
    obtain ⟨s,hs,hHs,⟨ds⟩⟩ := hmarked H H.property
    rcases factors_eq_or_centralize dt ds hcore hs with he | hc
    · exact (hne (Subtype.ext (hKt.trans (he.symm.trans hHs.symm)))).elim
    · simpa only [hKt,hHs] using hc
  refine ⟨{ factors := F
            marked := hmarked
            commute := fun K H hne x y hx hy => mem_centralizer_iff.mp (hc K H hne hy) x hx
            independent := ?_
            join_eq := ?_ }⟩
  · intro K
    obtain ⟨t,_,hKt,⟨dt⟩⟩ := hmarked K K.property
    have hh : (⨆ H : {K // K ∈ F}, ⨆ (_ : H ≠ K), H.val) ≤
        centralizer (K.val : Set G) :=
      iSup_le fun H => iSup_le fun hne => hc K H hne.symm
    exact (hKt.symm ▸ dt.disjoint).mono_right hh
  · apply top_unique
    rw [←hgen]
    apply (closure_le _).mpr
    intro t ht
    by_cases ht1 : t = 1
    · rw [ht1]; exact one_mem _
    · let K := normalClosure ({t} : Set G)
      have hK : K ∈ F := Set.mem_toFinset.mpr ⟨t,ht,ht1,rfl⟩
      exact (le_iSup (fun K : {K // K ∈ F} => K.val) ⟨K,hK⟩)
        (subset_normalClosure (Set.mem_singleton t))

namespace NaturalFactorProduct
open Representation.BinaryOffender
private theorem rank_one_square
    {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ) (t : G)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) ≤ 1) :
    t ^ 2 = 1 := by
  let e := LinearEquiv.ofBijective (ρ t) (ρ.apply_bijective t)
  obtain ⟨f,v,he⟩ := LinearEquiv.mem_dilatransvections_iff_finrank.mpr
    (show Module.finrank (ZMod 2) (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1 from hr)
  have he' (x : V) : e x = x + f x • v :=
    congrArg (fun l : V →ₗ[ZMod 2] V => l x) he
  have hfv : f v = 0 := by
    rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) (f v) with hz | ho
    · exact hz
    have hev : e v = 0 := by rw [he',ho,one_smul,ZModModule.add_self]
    have hv := e.map_eq_zero_iff.mp hev
    rw [hv,map_zero] at ho
    exact (zero_ne_one ho).elim
  apply hf
  ext x
  rw [pow_two,map_mul,map_one]
  change e (e x) = x
  rw [he',he',map_add,map_smul,hfv,smul_zero,add_zero]
  simp only [add_assoc,ZModModule.add_self,add_zero]
end NaturalFactorProduct

/-- An FF action generated by binary rank-one operators is the direct product
of its actual classified transvection closures. -/
theorem transvection_product_of_rank_one_generated
    {G V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V)
    (hff : ChapterB.SourceInduction.FFHypothesis KnownSimple.IsKnownSimple ρ)
    (hgen : closure {t : G | Module.finrank (ZMod 2)
      (LinearMap.range (ρ t-LinearMap.id)) ≤ 1} = ⊤) :
    Nonempty (TransvectionProductModel ρ) := by
  let := hff.finite_module
  apply transvection_product_of_generated ρ _ hgen hff.twoCore
  intro t ht ht1
  change Module.finrank (ZMod 2) (LinearMap.range (ρ t-LinearMap.id)) ≤ 1 at ht
  have hr : Module.finrank (ZMod 2) (LinearMap.range (ρ t-LinearMap.id)) = 1 := by
    have hne : Module.finrank (ZMod 2) (LinearMap.range (ρ t-LinearMap.id)) ≠ 0 := by
      intro hz
      have he : ρ t-LinearMap.id = 0 :=
        LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)
      exact ht1 (hff.faithful (by rw [map_one]; exact sub_eq_zero.mp he))
    omega
  obtain ⟨d⟩ := transvection_orbit_model hff t
    (NaturalFactorProduct.rank_one_square ρ hff.faithful t ht) ht1 hr
  exact d.factor_of_rank_one_generated hgen

/-- The full product, with the original module marking on every surviving
S₃, L₃(2), or S₅ factor. -/
structure SmallTransvectionProductModel
    {G V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) extends TransvectionProductModel ρ where
  small : ∀ K ∈ factors, ∃ U : Submodule (ZMod 2) V, SmallFactorModel ρ K U

/-- Apply the ambient component exclusions to every member of the assembled
factor family, preserving the entire product and the original representation. -/
theorem TransvectionProductModel.sieve
    {G V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) G V} (d : TransvectionProductModel ρ)
    (hAlt : ∀ K : Subgroup G, IsComponent G K → ∀ m, 6 ≤ m →
      ¬ Nonempty ((K ⧸ center K) ≃* alternatingGroup (Fin m)))
    (hBin : ∀ K : Subgroup G, IsComponent G K → ∀ m, m = 4 ∨ m = 5 →
      ¬ Nonempty ((K ⧸ center K) ≃* BinaryLinear.OuterCyclic.LinearGroup m)) :
    Nonempty (SmallTransvectionProductModel ρ) := by
  refine ⟨{ toTransvectionProductModel := d, small := ?_ }⟩
  intro K hK
  obtain ⟨t,_,rfl,⟨dt⟩⟩ := d.marked K hK
  exact ⟨dt.space.toSubmodule, factor_model_small_of_component_exclusions ρ hAlt hBin _
    (inferInstance : (normalClosure ({t} : Set G)).Normal).isSubnormal _ dt.model⟩


/-- The exact residual alternative for one literal factor under a central cover.
The nonsolvable branch uses the residual of the full preimage, both original
maps, and normalization by every cubic in the ambient group. -/
@[expose] def FactorResidualLift
    {A B N : Type*} [Group A] [Group B] [Group N]
    (φ : A →* B) (j : A →* N) (Q : Subgroup N) (K : Subgroup B) : Prop :=
  (Nonempty (K ≃* Equiv.Perm (Fin 3)) ∧ Nat.card (pResidual 2 K) = 3) ∨
  (let D := (solvableResidual K).map K.subtype
   (pResidual 2 K).map K.subtype = D ∧
   ∃ C : Subgroup A,
     C = (solvableResidual (K.comap φ)).map (K.comap φ).subtype ∧
     IsComponent A C ∧ C.map φ = D ∧
     IsComponent N (C.map j) ∧
     Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧
     C.map j ≤ Q ∧
     (∀ c : N, c ^ 3 = 1 → c ∈ normalizer (C.map j : Set N)) ∧
     (Nonempty ((D ⧸ center D) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
      Nonempty ((D ⧸ center D) ≃* alternatingGroup (Fin 5))))

/-- Every member of the full small-factor product has the literal residual
lift, not merely an isomorphic component chosen independently of the factor. -/
theorem SmallTransvectionProductModel.residual_lifts
    {B V : Type v} [Group B] [Finite B] [AddCommGroup V] [Module (ZMod 2) V]
    {A N : Type*} [Group A] [Finite A] [Group N]
    {ρ : Representation (ZMod 2) B V} (d : SmallTransvectionProductModel ρ)
    (φ : A →* B) (hs : Function.Surjective φ) (hk : φ.ker ≤ center A)
    (j : A →* N) (Q : Subgroup N)
    (hnorm : ∀ K : Subgroup N, IsComponent N K → ∀ c : N,
      c ^ 3 = 1 → c ∈ normalizer (K : Set N))
    (hlift : ∀ D : Subgroup B, IsComponent B D →
      ∃ C : Subgroup A, IsComponent A C ∧ C.map φ = D ∧
        IsComponent N (C.map j) ∧
        Nonempty (((C.map j) ⧸ center (C.map j)) ≃* (D ⧸ center D)) ∧ C.map j ≤ Q) :
    ∀ K ∈ d.factors, FactorResidualLift φ j Q K := by
  intro K hK
  obtain ⟨U,hU⟩ := d.small K hK
  have hsub : K.IsSubnormal := by
    obtain ⟨t,_,rfl,_⟩ := d.marked K hK
    exact (inferInstance : (normalClosure ({t} : Set B)).Normal).isSubnormal
  rcases small_factor_residual_alternatives ρ K hsub U hU with hthree | ⟨hD,hr,heD⟩
  · exact Or.inl hthree
  · obtain ⟨C,hC,hCD,hCN,he,hCQ⟩ := hlift _ hD
    exact Or.inr ⟨hr,C,
      NaturalFactorSieve.component_eq_factor_residual_preimage φ hs hk K C hC hCD,
      hC,hCD,hCN,he,hCQ,hnorm _ hCN,heD⟩


end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
