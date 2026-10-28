module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorAlphaCore
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalKernelMarking

/-!
# Naturality of the whole nontrivial strict alpha actor kernel

The actual smaller core lies in the alpha center. It is normalized by the
smaller actor, and the whole vertex core centralizes that center; supplementation
therefore makes it invariant under the intrinsic local actor. Its genuine
natural action has no proper nonzero invariant subgroup, so the whole smaller
core maps onto Z_alpha. The original covering is injective on this actor and
transports those natural coordinates to its entire kernel.

The quotient marking comes from the source natural center action. No natural
kernel, section selection, or reduced-model comparison is assumed. The
nonzero core and literal Cartan-kernel condition are retained, as required
at the failed-exchange branch of DGS (14.9)(c), pp.215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam Representation
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction Noncommuting NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
universe uG
variable {G : Type uG} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S

private theorem natural_center_coordinates
    (h : HypothesisF11 L S) {v m w : Vertex F}
    (hc : IsCriticalPair F v w) (hne : ⁅Z F v,Z F w⁆≠⊥)
    (hb : b F=2) (hvm : (graph F).Adj v m) (hmw : (graph F).Adj m w) :
    ∃ (k : Type uG) (_ : Field k) (_ : Finite k) (_ : CharP k 2)
      (_ : Algebra (ZMod 2) k),
      ∃ (π : graphLocalGroup F v →* SL(2,k))
        (e : (graphLocalGroup F v ⧸ pCore 2 (graphLocalGroup F v)) ≃* SL(2,k)),
        Function.Surjective π ∧ π.ker=pCore 2 (graphLocalGroup F v) ∧
        (∀ x, e (QuotientGroup.mk' (pCore 2 (graphLocalGroup F v)) x)=π x) ∧
        Nonempty (BinaryConjugationSection (graphLocalGroup F v) (Z F v) ⊥
          (SL2NaturalOffenders.NoStrong.natural.comp π)) := by
  obtain ⟨k,f,fin,alg,π,hπ,hker,⟨d⟩⟩ :=
    (reduced_critical_natural_centers_and_products h hc hne).1
  let _ : CharP k 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) k).injective 2
  let J := graphLocalGroup F v
  have hcore : (Q F v).subgroupOf J=pCore 2 J := by
    have hh : J.pCoreIn 2=Q F v := CommutingTrivial.graphLocalGroup_core (reduced_triple h) v
    rw [←hh]
    exact comap_map_eq_self_of_injective J.subtype_injective _
  have hker' : π.ker=pCore 2 J := hker.trans hcore
  let e : (J ⧸ pCore 2 J) ≃* SL(2,k) :=
    (QuotientGroup.quotientMulEquivOfEq hker'.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective π hπ)
  have hz := (reduced_bTwo_center_identities h hc hne hb hvm hmw).2.1
  change center J=⊥ at hz
  have hω : Stellmacher.omegaOneCenterAmbient J=⊥ := by
    apply bot_unique
    intro z hzω
    obtain ⟨hzJ,_,hzC⟩ := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hzω
    have hm : (⟨z,hzJ⟩:J)∈center J :=
      mem_center_iff.mpr (fun x => Subtype.ext (hzC x x.property))
    rw [hz,mem_bot] at hm
    exact congrArg Subtype.val hm
  exact ⟨k,f,fin,inferInstance,alg,π,e,hπ,hker',fun _ => rfl,⟨hω ▸ d⟩⟩

variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))

/-- A nonzero actual alpha small-actor core is exactly the natural center,
and its whole kernel has genuine source natural coordinates. -/
theorem strict_source_small_actor_alpha_natural
    {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=12)
    (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)
    (hCU : (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 6))≠⊥)
    (htype : ((bOne_tree_cover h).vertex (p.getVert 6)).type=false)
    (hcore : pCore 2 (halfPathActor (X := (A).Universal) p 6)≠⊥) :
    ((halfPathActor (X := (A).Universal) p 6).pCoreIn 2).map (bOne_tree_map h)=
      Z F ((bOne_tree_cover h).vertex (p.getVert 6)) ∧
      ∃ (k : Type uG) (_ : Field k) (_ : Finite k) (_ : CharP k 2),
        4≤Nat.card k ∧
        ∃ e : (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)) ⧸
          pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))) ≃* SL(2,k),
          Function.Surjective (halfPathLinearMap h p 6 hl e) ∧
          (halfPathLinearMap h p 6 hl e).ker=pCore 2 (halfPathActor (X := (A).Universal) p 6) ∧
          Nonempty (NaturalCubic.NaturalKernel (halfPathLinearMap h p 6 hl e)) := by
  let D := halfPathActor (X := (A).Universal) p 6
  let φ := bOne_tree_map h
  let δ := φ.comp D.subtype
  let v := (bOne_tree_cover h).vertex (p.getVert 6)
  let J := graphLocalGroup F v
  let M := D.map φ
  let V := (D.pCoreIn 2).map φ
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  have hδ : Function.Injective δ := by
    intro x y he
    exact halfPathLocalMap_injective h p 6 hl (Subtype.ext he)
  have hVZ : V≤Z F v := strict_source_small_actor_alpha_core_le_center
    h hc hne hb hβu hns hlinear p hp hl hT hCU htype
  have hVne : V≠⊥ := by
    intro he
    apply hcore
    apply _root_.eq_bot_iff.mpr
    intro x hx
    have hm : δ x∈V := ⟨x,⟨x,hx,rfl⟩,rfl⟩
    exact hδ ((he.le hm).trans δ.map_one.symm)
  obtain ⟨g,hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  change g • base F v.type=v at hg
  rw [htype] at hg
  let m := g • base F true
  let w := g • u
  have hcm : IsCriticalPair F v w := by
    simpa only [hg] using criticalPair_translate F hc g
  have hnc : ⁅Z F v,Z F w⁆≠⊥ := by
    rw [←hg,Z_translate,Z_translate,←map_commutator]
    intro he
    exact hne (Subgroup.map_injective (MulAut.conj g).injective
      (he.trans (Subgroup.map_bot _).symm))
  have hvm : (graph F).Adj v m := by
    have hh := (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj
      (show (graph F).Adj (base F false) (base F true) from
        ⟨by change false≠true; decide,Subgroup.CosetGeometry.incident_base _ _ _⟩)
    change (graph F).Adj (g • base F false) m at hh
    simpa only [hg] using hh
  have hmw : (graph F).Adj m w :=
    (Subgroup.CosetGeometry.translationGraphIso F g).toHom.map_adj hβu
  obtain ⟨k,fk,fink,chk,alg,π,e,hπ,hπker,he,⟨c⟩⟩ :=
    natural_center_coordinates h hcm hnc hb hvm hmw
  have hci : Function.Injective c.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [c.kernel_eq,bot_subgroupOf]
  have hMV : M≤normalizer (V : Set (G₀ L S)) :=
    (map_mono (D.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image D (pCore 2 D)))).trans
        ((D.pCoreIn 2).le_normalizer_map φ)
  obtain ⟨K,fK,finK,chK,hK,eK,hactors⟩ :=
    strict_source_small_actor_linear_quotients h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨hontoK,hkernel,hsup,_⟩ := hactors p hp hl hT
  change M ⊔ Q F v=J at hsup
  have hJV : J≤normalizer (V : Set (G₀ L S)) := by
    rw [←hsup]
    apply sup_le hMV
    exact ((graph_Q_centralizes_Z (reduced_triple h) v).trans
      (centralizer_le hVZ)).trans (Subgroup.centralizer_le_normalizer _)
  have hVeq : V=Z F v := by
    obtain ⟨x,hx,hxne⟩ := V.bot_or_exists_ne_one.resolve_left hVne
    let xZ : Z F v := ⟨x,hVZ hx⟩
    have hx0 : (c.coordinates xZ).toAdd≠0 := by
      intro hh
      have hh' := hci ((Multiplicative.toAdd.injective hh).trans c.coordinates.map_one.symm)
      exact hxne (congrArg Subtype.val hh')
    apply le_antisymm hVZ
    intro z hz
    by_cases hz1 : z=1
    · exact hz1 ▸ V.one_mem
    let zZ : Z F v := ⟨z,hz⟩
    have hz0 : (c.coordinates zZ).toAdd≠0 := by
      intro hh
      have hh' := hci ((Multiplicative.toAdd.injective hh).trans c.coordinates.map_one.symm)
      exact hz1 (congrArg Subtype.val hh')
    obtain ⟨y,hy⟩ := Matrix.SL2.exists_mulVec_eq k (c.coordinates xZ).toAdd (c.coordinates zZ).toAdd hx0 hz0
    obtain ⟨l,rfl⟩ := hπ y
    have hc := c.equivariant l xZ
    change (c.coordinates _).toAdd=Matrix.mulVec (π l).val (c.coordinates xZ).toAdd at hc
    have heq := hci (Multiplicative.toAdd.injective (hc.trans hy))
    have hzval : (l:G₀ L S)*x*(l:G₀ L S)⁻¹=z := congrArg Subtype.val heq
    exact hzval ▸ (mem_normalizer_iff.mp (hJV l.property) x).mp hx
  let f := halfPathLinearMap h p 6 hl e
  have hfe (x : D) : f x=π (halfPathLocalMap h p 6 hl x) := he _
  have hfker : f.ker=pCore 2 D := by
    rw [halfPathLinearMap_kernel] at hkernel
    rw [halfPathLinearMap_kernel]
    exact hkernel
  have honto : Function.Surjective f := by
    intro y
    obtain ⟨x,hx⟩ := hontoK ((eK v) (e.symm y))
    have hq : QuotientGroup.mk' (pCore 2 J) (halfPathLocalMap h p 6 hl x)=e.symm y :=
      (eK v).injective hx
    refine ⟨x,?_⟩
    change e (QuotientGroup.mk' (pCore 2 J) (halfPathLocalMap h p 6 hl x))=y
    rw [hq,e.apply_symm_apply]
  have hk4 : 4≤Nat.card k := (hK v.type).trans_eq
    (Matrix.SL2.field_card_eq_of_equiv ((eK v).symm.trans e))
  refine ⟨hVeq,k,fk,fink,chk,hk4,e,honto,hfker,?_⟩
  let κ : f.ker →* Z F v :=
    { toFun x := ⟨δ x,hVeq ▸ (show δ x∈V from ⟨x,⟨x,hfker ▸ x.property,rfl⟩,rfl⟩)⟩
      map_one' := Subtype.ext δ.map_one
      map_mul' x y := Subtype.ext (δ.map_mul x y) }
  have hκ : Function.Bijective κ := by
    constructor
    · intro x y heq
      exact Subtype.ext (hδ (congrArg Subtype.val heq))
    · intro z
      have hzV : (z:G₀ L S)∈V := hVeq.symm ▸ z.property
      obtain ⟨x,⟨y,hy,rfl⟩,heq⟩ := hzV
      exact ⟨⟨y,hfker.symm ▸ hy⟩,Subtype.ext heq⟩
  refine ⟨⟨(MulEquiv.ofBijective κ hκ).trans (MulEquiv.ofBijective c.coordinates ⟨hci,c.onto⟩),?_⟩⟩
  intro x z
  change c.coordinates (κ ⟨x*z*x⁻¹,_⟩)=Matrix.SL2.naturalAction k (f x) (c.coordinates (κ z))
  have heq : κ ⟨x*z*x⁻¹,(inferInstance : f.ker.Normal).conj_mem z z.property x⟩=
      ⟨(halfPathLocalMap h p 6 hl x:G₀ L S)*(κ z:G₀ L S)*
        (halfPathLocalMap h p 6 hl x:G₀ L S)⁻¹,
        (mem_normalizer_iff.mp (c.normalized (halfPathLocalMap h p 6 hl x).property) _).mp (κ z).property⟩ := by
    apply Subtype.ext
    exact map_mul δ _ _ |>.trans (by rw [map_mul,map_inv]; rfl)
  rw [heq,hfe]
  exact Multiplicative.toAdd.injective (c.equivariant (halfPathLocalMap h p 6 hl x) (κ z))

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
