module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OrthogonalCubic
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalComplement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.SylowFixed
public import Theory.GroupTheory.CoprimeQuotientSubgroups.ElementLift
public import Theory.GroupTheory.PerfectHalfOrderImage
public import Theory.Representation.FirstCohomologyDuality.SimpleCover
/-!
# The cubic and non-two-index conditions on the original hyperplane

The original binary complement is the injective image of a field complement
in the nonsplit orthogonal cover. Its cubic isometry lifts through the
original two-core quotient with order three, normalizes the same subgroup U,
and still moves its covered vector. Thus its cyclic subgroup acts faithfully
on U in the exact sense required by E.6.14.

If the stabilizer in L join T had index two, perfectness would place L in
that stabilizer. The corresponding field complement would then be invariant
under the full derived symplectic action, contradicting the commutator
generation of the orthogonal cover. The final consumer leaves only maximality
of this stabilizer to qt-d-1222-natural-weak-parameters. The existing producers
of the earlier-source premises retain their final discharge with
qt-d-1222-natural-weak-closure-source.

Source: Aschbacher--Smith, 11.2.2, printed p.767, and E.6.14.
-/

open Subgroup Representation
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes
open CFSG.Quasithin.ChapterE CFSG.Quasithin.ChapterE.Section06
open CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces
open Representation.SymplecticFourOrthogonalCover hiding L
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalCubic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

omit [Finite G] in
private theorem faithful_three_of_element {U : Subgroup G} {x : G}
    (hx : x ∈ normalizer (U : Set G)) (ho : orderOf x = 3)
    (hm : x ∉ centralizer (U : Set G)) : HasFaithfulThreeAction U := by
  let A := zpowers x
  have hA : A ≤ normalizer (U : Set G) := zpowers_le.mpr hx
  have hc : Nat.card A = 3 := (Nat.card_zpowers x).trans ho
  let : IsSimpleGroup A := isSimpleGroup_of_prime_card hc
  let k := U.normalizerMonoidHom.comp (inclusion hA)
  refine ⟨A,hA,hc,k.ker_eq_bot_iff.mp ?_⟩
  exact ((inferInstance : k.ker.Normal).eq_bot_or_eq_top).resolve_right (by
    intro hk
    have hh : (⟨x,mem_zpowers x⟩ : A) ∈ k.ker := hk.symm ▸ mem_top _
    have he : inclusion hA (⟨x,mem_zpowers x⟩ : A) ∈ U.normalizerMonoidHom.ker := hh
    rw [normalizerMonoidHom_ker] at he
    exact hm he)

/-- The actual component contains a cubic faithful on the original hyperplane. -/
theorem exists_original_cubic
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hn : S.field.degree = 2)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    ∃ x ∈ L, x ∈ normalizer (U : Set G) ∧ orderOf x = 3 ∧
      x ∉ centralizer (U : Set G) := by
  obtain ⟨f,_,_,Q,hQ,hQR,him,hker,hgreat,_⟩ :=
    OriginalComplement.exists_original_field_complement D S m hUV hU hC hint
  obtain ⟨g,hg,hgQ,x,hxQ,hgx⟩ := OrthogonalCubic.exists_cubic
    (by rw [S.field.card_eq,hn]; norm_num) Q hQR hQ
  let c := Coordinates.sp4 m
  have hk : c.quotientMap.ker = pCore 2 L := by
    ext l
    change c.groupEquiv (QuotientGroup.mk' (pCore 2 L) l) = 1 ↔ l ∈ pCore 2 L
    rw [map_eq_one_iff _ c.groupEquiv.injective]
    exact QuotientGroup.eq_one_iff l
  have hcop : Nat.Coprime 3 (Nat.card c.quotientMap.ker) := by
    obtain ⟨n,he⟩ := (show IsPGroup 2 (pCore 2 L) from pCore_isPGroup).exists_card_eq
    rw [hk,he]
    exact Nat.Coprime.pow_right n (by decide)
  obtain ⟨l,hl,hlp⟩ := exists_prime_exponent_lift c.quotientMap c.quotientMap_surjective
    hcop g (hg ▸ pow_orderOf_eq_one g)
  have hlo : orderOf l = 3 := orderOf_eq_prime hlp (by
    intro h1
    have hg1 : g = 1 := hl.symm.trans (h1 ▸ c.quotientMap.map_one)
    simp only [hg1,orderOf_one] at hg
    omega)
  have hlN : (l : G) ∈ normalizer (U : Set G) :=
    (OriginalComplement.original_field_stabilizer_iff D S m f hUV Q him hgreat l).mp
      (hl.symm ▸ hgQ)
  refine ⟨l,l.property,hlN,(Subgroup.orderOf_coe l).trans hlo,?_⟩
  intro hfix
  have hfxU : (D.spaceEquiv (Multiplicative.ofAdd (f x)) : G) ∈ U := by
    apply (OriginalComplement.subspace_mem D U (f x)).mp
    rw [←him]
    exact ⟨x,hxQ,rfl⟩
  have hfx : Preliminary.markedAction D m g (f x) = f x := by
    apply Multiplicative.ofAdd.injective
    apply D.spaceEquiv.injective
    apply Subtype.ext
    rw [←hl,OriginalComplement.markedAction_ambient D S m]
    rw [← Subgroup.mem_centralizer_iff.mp hfix _ hfxU]
    exact mul_inv_cancel_right _ _
  let := S.source.quasisimple
  let : Group.IsPerfect (Matrix.symplecticGroup (Fin 2) S.field.Carrier) :=
    Group.IsPerfect.ofSurjective (f := m.groupEquiv.toMonoidHom) m.groupEquiv.surjective
  let g' : SymplecticFourOrthogonalCover.L (K := S.field.Carrier) :=
    ⟨g,Group.IsPerfect.mem_commutator⟩
  have heq : f (fullAction g x) = f x := by
    have he := LinearMap.congr_fun (f.isIntertwining' g') x
    exact he.trans hfx
  have hdelta : fullAction g x - x ∈ (⊥ : Submodule (ZMod 2) (Space (K := S.field.Carrier))) := by
    rw [←hker.eq_bot]
    refine ⟨Q.sub_mem ?_ hxQ,?_⟩
    · rw [←hgQ]
      exact ⟨x,hxQ,rfl⟩
    · change f (fullAction g x - x) = 0
      rw [map_sub,heq,sub_self]
  exact hgx (sub_eq_zero.mp hdelta)

/-- The same cubic gives the injective action required by E.6.14. -/
theorem faithful_three_of_original_complement
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (symplecticNatural (k := S.field.Carrier) 2)))
    (hn : S.field.degree = 2)
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hC : Nat.card ↥(V ⊓ centralizer (L : Set G)) = 2)
    (hint : U ⊓ (V ⊓ centralizer (L : Set G)) = ⊥) :
    HasFaithfulThreeAction U := by
  obtain ⟨x,_,hx,ho,hm⟩ := exists_original_cubic D S m hn hUV hU hC hint
  exact faithful_three_of_element hx ho hm

/-- The source reduction discharges the cubic hypothesis for every escaping hyperplane. -/
theorem escaping_hyperplane_faithful_three (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    HasFaithfulThreeAction U := by
  obtain ⟨⟨m⟩,hn,hC,hi,_⟩ := escaping_hyperplane_sp4_four D S c hE hunique hUV hU hescape
  exact faithful_three_of_original_complement D S m hn hUV hU hC hi

/-- Perfectness and the nonsplit cover exclude index two for the same stabilizer. -/
theorem escaping_hyperplane_index_ne_two (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hescape : ¬ centralizer (U : Set G) ≤ normalizer (L : Set G)) :
    (localNormalizer (L ⊔ (T : Subgroup G)) U).relIndex (L ⊔ (T : Subgroup G)) ≠ 2 := by
  intro hindex
  let K := L ⊔ (T : Subgroup G)
  let N := (localNormalizer K U).subgroupOf K
  let H := L.subgroupOf K
  let := CFSG.Quasithin.Chapter1.mem_L_isPerfect S.source.maximal_faithful.1.1
  let e : H ≃* L := subgroupOfEquivOfLe (show L ≤ K from le_sup_left)
  let : Group.IsPerfect H := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hcomm : commutator K ≤ N :=
    Theory.GroupTheory.PerfectHalfOrderImage.commutator_le_of_index_le_two N hindex.le
  have hHN : H ≤ N := calc
    H = ⁅H,H⁆ := H.commutator_eq_self.symm
    _ ≤ commutator K := Subgroup.commutator_mono le_top le_top
    _ ≤ N := hcomm
  have hLN : L ≤ normalizer (U : Set G) := by
    intro l hl
    exact (hHN (show (⟨l,(show L ≤ K from le_sup_left) hl⟩ : K) ∈ H from hl)).2
  obtain ⟨m,_,f,_,_,Q,hQ,hQR,_,_,_,_,_,hstab⟩ :=
    OriginalComplement.escaping_hyperplane_field_complement D S c hE hunique hUV hU hescape
  have hinv : ∀ g x, x ∈ Q → action g x ∈ Q := by
    intro g x hx
    obtain ⟨l,hl⟩ := (Coordinates.sp4 m).quotientMap_surjective g.val
    have hs := (hstab l).mpr (hLN l.property)
    rw [hl] at hs
    change fullAction g.val x ∈ Q
    rw [←hs]
    exact ⟨x,hx,rfl⟩
  have him : Q.map (projection (K := S.field.Carrier)).toLinearMap = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨w,hw⟩ := projection_surjective (K := S.field.Carrier) v
    have hwQR : w ∈ Q ⊔ radical := hQR.sup_eq_top.symm ▸ Submodule.mem_top
    obtain ⟨q,hq,r,hr,he⟩ := Submodule.mem_sup.mp hwQR
    refine ⟨q,hq,?_⟩
    have hr0 : projection (K := S.field.Carrier) r = 0 := hr
    change projection q = v
    rw [←hw,←he,map_add,hr0,add_zero]
  have htop := Representation.OneCohomology.invariant_eq_top_of_cover_image_eq_top
    (SymplecticFourOrthogonalCover.projection (K := S.field.Carrier)) projection_isCover Q hinv him
  have he := congrArg (fun P : Submodule S.field.Carrier (Space (K := S.field.Carrier)) =>
    Module.finrank S.field.Carrier P) htop
  rw [hQ,finrank_top,space_finrank] at he
  omega

/-- E.6.14 now needs only maximality of the actual stabilizer. The fixed
intersection, faithful cubic and non-two index are proved on that same U. -/
theorem centralizer_le_of_natural_maximal_stabilizer (c : Coordinates D S.field)
    (hE : HypothesisE61 CFSG.KnownSimple.IsKnownSimple T (normalizer (L : Set G)) V)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ≤ N → N = normalizer (L : Set G))
    {U : Subgroup G} (hUV : U ≤ V) (hU : subgroupCorank V U = 1)
    (hmax : localNormalizer (L ⊔ (T : Subgroup G)) U ⋖ L ⊔ (T : Subgroup G)) :
    centralizer (U : Set G) ≤ normalizer (L : Set G) := by
  by_contra hescape
  exact hescape (centralizer_le_of_natural_stabilizer_and_cubic D S c hE hunique hUV hU
    (escaping_hyperplane_faithful_three D S c hE hunique hUV hU hescape) hmax
    (escaping_hyperplane_index_ne_two D S c hE hunique hUV hU hescape))

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.Hyperplanes.OriginalCubic
