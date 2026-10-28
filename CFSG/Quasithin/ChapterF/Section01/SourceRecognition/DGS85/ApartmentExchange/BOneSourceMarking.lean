module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneFullCartanTransport

/-!
# Full Cartan markings from the original b=1 action

The earlier source Borel lifts the entire normalizer of its marked SL₂
Sylow subgroup. Choose one inner matrix marking which makes that Sylow
upper unipotent and the actual odd actor Cartan diagonal. In the original
factorization B = UK, the image of U is a two-subgroup of this normalizer,
hence lies in its upper unipotent Sylow. Comparing diagonal entries of the
lifted product proves that the Cartan image contains every diagonal matrix.
Thus diagonal containment, full-diagonal surjectivity and neighbor-triangular
markings are constructed together, using the same original covering map.

Apply these markings to the central natural kernel and a supplied element
of the genuine path radical whose original image lies in the neighbor center
outside the endpoint core. The construction derives its upper-root parameter
and involution relation and produces a whole-Cartan reflection, retaining the
full local-kernel centralization clause. Its conjugacy formula retains the
actual actor-center correction. No coordinate or root-image marking is an
input to this application.

The nonbinary scalar, natural-module dimension and actual root element remain
explicit. Removing the central correction in the nontrivial-center branch,
selecting these roots from the earlier geometry, the binary and other source
branches, exchange and quotient root signs remain separate obligations.
This does not prove the complete conjugacy clause of (14.2) or (14.19).

Source: DGS, *Groups and Graphs* (1985), (10.5), printed pp.155--157,
and (14.1)--(14.2), pp.210--211, with the universal tree convention p.208.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups Pointwise
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable (h : HypothesisF11 L S) (c : CompatibleCartans L (reducedSylow L S)) (i : Bool)
variable (d : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
  (base (reducedFamily L S) (!i)) F W)
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem marking_middle_le (j : Bool) : originalMiddle (reducedAmalgam L S)≤
    Universal.cosetFamily (reducedAmalgam L S) j := by
  rw [originalMiddle,←Universal.overlap_eq _
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases j
  · exact inf_le_left
  · exact inf_le_right

/-- The same inner marking makes the genuine Cartan image the full diagonal
 torus and makes every original neighbor stabilizer upper triangular. -/
theorem exists_full_cartan_neighbor_marking
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) (!i))=
      Z (reducedFamily L S) (base (reducedFamily L S) (!i))) :
    ∃ a : SL(2,F),
      (∀ k : universalBOneActor h i d, (k:(reducedAmalgam L S).Universal)∈cartan c →
        ∃ b : F, ∃ hb : b≠0, a*universalBOneQuotient h i d k*a⁻¹=
          Matrix.SpecialLinearGroup.diag2 b hb) ∧
      (∀ b : F, ∀ hb : b≠0, Matrix.SpecialLinearGroup.diag2 b hb∈
        ((cartan c).subgroupOf (universalBOneActor h i d)).map
          ((MulAut.conj a).toMonoidHom.comp (universalBOneQuotient h i d))) ∧
      (∀ k : d.actor, (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
        (base (reducedFamily L S) (!i)) → (a*d.quotient k*a⁻¹).val 1 0=0) ∧
      (d.imageSylow : Subgroup SL(2,F)).map (MulAut.conj a).toMonoidHom=
        Matrix.SpecialLinearGroup.upperUnipotent F := by
  let A := reducedAmalgam L S
  let H := universalBOneActor h i d
  let e := universalBOneActorEquiv h i d
  let K := (cartan c).subgroupOf H
  let K' := K.map e.toMonoidHom
  let := (reduced_hypothesis h).finite_commonBorel
  let : Finite (cartan c) := Finite.of_surjective
    ((middleMap L S).subgroupMap ((c.D 0⊔c.D 1).subgroupOf (commonBorel L (reducedSylow L S))))
    ((middleMap L S).subgroupMap_surjective _)
  have hodd : Nat.Coprime 2 (Nat.card K') := by
    rw [card_map_of_injective e.injective]
    apply (cartan_odd c).of_dvd_right
    have he := card_map_of_injective (f := H.subtype) (K := K) H.subtype_injective
    rw [←he,subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  have neighbor_mem (y : H) (hy : (y:A.Universal)∈originalMiddle A) :
      (e y:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
        (base (reducedFamily L S) (!i)) := by
    rw [RankTwo.stabilizer,stabilizer_base]
    change bOne_tree_map h y∈reducedFamily L S (!i)
    rw [←(bOne_tree_cover h).map_eq (!i)]
    exact mem_map_of_mem _ (marking_middle_le (!i) hy)
  have hK : ∀ k∈K', (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
      (base (reducedFamily L S) (!i)) := by
    rintro k ⟨y,hy,rfl⟩
    exact neighbor_mem y (cartan_le c hy)
  obtain ⟨a,ha,hdiag,htri⟩ := BOneActor.exists_cartan_neighbor_marking
    (reduced_triple h) d K' hK hodd
  let π := (MulAut.conj a).toMonoidHom.comp (universalBOneQuotient h i d)
  have hdiag' (k : H) (hk : (k:A.Universal)∈cartan c) :
      ∃ b : F, ∃ hb : b≠0, π k=Matrix.SpecialLinearGroup.diag2 b hb :=
    hdiag (e k) (mem_map_of_mem e.toMonoidHom hk)
  refine ⟨a,hdiag',?_,htri,ha⟩
  have hn : (B₀ L S).subgroupOf (G₀ L S)≤normalizer (d.actor : Set (G₀ L S)) := by
    rw [hactor]
    exact reduced_borel_normalizes_source_actor h _
  have hUB : ((twoGroup L S).subgroupOf H).map π≤
      Matrix.SpecialLinearGroup.rankOneBorel F := by
    rintro y ⟨x,hx,rfl⟩
    exact (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff _).mpr
      (htri (e x) (neighbor_mem x (twoGroup_le hx)))
  have hUp : IsPGroup 2 (((twoGroup L S).subgroupOf H).map π) :=
    (twoGroup_isTwo h).comap_subtype.map π
  have hUU : ((twoGroup L S).subgroupOf H).map π≤
      Matrix.SpecialLinearGroup.upperUnipotent F := by
    have he := hUp.inf_normalizer_sylow (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
    change ((twoGroup L S).subgroupOf H).map π ⊓ Matrix.SpecialLinearGroup.rankOneBorel F =
      ((twoGroup L S).subgroupOf H).map π ⊓ Matrix.SpecialLinearGroup.upperUnipotent F at he
    rw [inf_eq_left.mpr hUB] at he
    exact inf_eq_left.mp he.symm
  intro b hb
  have hbN : Matrix.SpecialLinearGroup.diag2 b hb∈
      normalizer (Matrix.SpecialLinearGroup.upperUnipotent F : Set SL(2,F)) := by
    exact (Matrix.SpecialLinearGroup.mem_rankOneBorel_iff _).mpr (by
      simp [Matrix.SpecialLinearGroup.diag2_coe'])
  rw [←ha,←map_equiv_normalizer_eq] at hbN
  obtain ⟨v,hv,hva⟩ := hbN
  obtain ⟨k,hk,hπk⟩ := base_borel_lifts_sylow_normalizer (reduced_triple h) i d hcore hn v hv
  let y := e.symm k
  have hyB : (y:A.Universal)∈originalMiddle A := by
    have hky : bOne_tree_map h y=(k:G₀ L S) := congrArg Subtype.val (e.apply_symm_apply k)
    have hkm : (k:G₀ L S)∈(originalMiddle A).map (bOne_tree_map h) := by
      rw [originalMiddle,←Universal.overlap_eq A
        (inclusion_injective (commonBorel_le_parabolic 0))
        (inclusion_injective (commonBorel_le_parabolic 1))]
      change (k:G₀ L S)∈(Universal.cosetFamily A false ⊓ Universal.cosetFamily A true).map (bOne_tree_map h)
      rw [(bOne_tree_cover h).map_inf]
      exact (reduced_triple h).intersection.symm ▸ hk
    obtain ⟨z,hz,hzy⟩ := hkm
    have he := (bOne_tree_cover h).injective i
      (a₁ := ⟨z,marking_middle_le i hz⟩) (a₂ := ⟨y,y.property.2⟩) (hzy.trans hky.symm)
    exact (congrArg Subtype.val he) ▸ hz
  have hπy : π y=Matrix.SpecialLinearGroup.diag2 b hb := by
    change a*d.quotient (e (e.symm k))*a⁻¹=_
    rw [e.apply_symm_apply,hπk]
    exact hva
  have hyprod : (y:A.Universal)∈(twoGroup L S : Set A.Universal)*(cartan c : Set A.Universal) := by
    rw [←factorization_set h c]
    exact hyB
  obtain ⟨u,hu,k,hk,huk⟩ := hyprod
  have huH := twoGroup_le_bOneActor h i d hactor hu
  have hkH : k∈H := by
    have hm := H.mul_mem (H.inv_mem huH) y.property
    rwa [←huk,inv_mul_cancel_left] at hm
  let uH : H := ⟨u,huH⟩
  let kH : H := ⟨k,hkH⟩
  have he : uH*kH=y := Subtype.ext huk
  have huU := hUU (mem_map_of_mem π (show uH∈(twoGroup L S).subgroupOf H from hu))
  obtain ⟨t,ht⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F (π uH)).mp huU
  obtain ⟨b',hb',hkdiag⟩ := hdiag' kH hk
  have hmul : π uH*π kH=Matrix.SpecialLinearGroup.diag2 b hb := by rw [←map_mul,he,hπy]
  have hscalar := congrArg (fun v : SL(2,F) => v.val 0 0) hmul
  rw [←ht,hkdiag] at hscalar
  have hbb : b'=b := by
    simpa [Matrix.SpecialLinearGroup.transvection_coe,Matrix.SpecialLinearGroup.diag2_coe',
      Matrix.SpecialLinearGroup.coe_mul,Matrix.mul_apply,Fin.sum_univ_two] using hscalar
  exact ⟨kH,hk,by simpa only [hbb] using hkdiag⟩

/-- Whole-Cartan reflection selection with all diagonal, full-diagonal and
neighbor-triangular markings constructed from the original source action.
The central factor in root conjugacy remains explicit. -/
theorem source_bOne_full_cartan_reflection_of_neighbor
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hneighbor : Q (reducedFamily L S) (base (reducedFamily L S) (!i))=
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (b : F) (hb : b≠0) (hb1 : b≠1)
    {v : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk v
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (x : universalBOneActor h i d)
    (hxR : (x:(reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal) p)
    (hxZ : bOne_tree_map h x∈Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hxQ : bOne_tree_map h x∉Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    ∃ t : (reducedAmalgam L S).Universal,
      t∈universalBOneActor h i d ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i=
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t=1 ∧ orderOf t=2 ∧ t∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) p,
        orderOf y=2 ∧ ∃ z∈centerIn (universalBOneActor h i d),
          bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
          ∃ g∈universalBOneActor h i d, g*(z*y)*g⁻¹=t) ∧
      ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  obtain ⟨m,hdiag,hfull,htri,hmSylow⟩ := exists_full_cartan_neighbor_marking h c i d hactor hneighbor
  let A := reducedAmalgam L S
  let H := universalBOneActor h i d
  let π := (MulAut.conj m).toMonoidHom.comp (universalBOneQuotient h i d)
  let nat := (universalBOneNaturalCentralKernel h i d hcore E).conj m
  let e := universalBOneActorEquiv h i d
  let : ∀ j, Finite (reducedFamily L S j) := finite_endpoints (reduced_triple h)
  let : Finite d.actor := Finite.of_injective (inclusion d.actor_le) (inclusion_injective _)
  let : Finite H := Finite.of_equiv d.actor e.symm.toEquiv
  let := (reduced_hypothesis h).finite_commonBorel
  let : Finite (cartan c) := Finite.of_surjective
    ((middleMap L S).subgroupMap ((c.D 0⊔c.D 1).subgroupOf (commonBorel L (reducedSylow L S))))
    ((middleMap L S).subgroupMap_surjective _)
  let := cartan_abelian h c
  have honto : Function.Surjective π := (MulAut.conj m).surjective.comp (d.onto.comp e.surjective)
  have hn := universalBOneActor_normalized h i d c hactor
  have hcenter : center H≤π.ker := by
    intro z hz
    have hc : π z∈center SL(2,F) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨u,rfl⟩ := honto y
      simpa only [map_mul] using congrArg π (Subgroup.mem_center_iff.mp hz u)
    rwa [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hc
  have kernel_core (z : H) (hz : z∈π.ker) :
      bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) := by
    have hm : e z∈d.quotient.ker :=
      (MulAut.conj m).injective (hz.trans (map_one _).symm)
    rw [d.kernel] at hm
    exact hm
  have hsquare (z : π.ker) : z*z=1 := by
    have hzQ := kernel_core z z.property
    have hzZ : bOne_tree_map h z∈Z (reducedFamily L S) (base (reducedFamily L S) i) := hcore ▸ hzQ
    have hs := ((mem_omegaCenterIn_iff _ _).mp
      ((source_Z_Q_U (reduced_triple h) (base (reducedFamily L S) i)).1 hzZ)).2.2
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_one,map_mul,map_one,e,
      universalBOneActorEquiv,coveredActorEquiv_apply,pow_two] using hs
  have hxS : d.quotient (e x)∈(d.imageSylow : Subgroup SL(2,F)) := by
    rw [←d.neighbor_image]
    exact mem_map_of_mem d.quotient hxZ
  have hxU : π x∈Matrix.SpecialLinearGroup.upperUnipotent F :=
    hmSylow ▸ mem_map_of_mem (MulAut.conj m).toMonoidHom hxS
  obtain ⟨a,haimage⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F (π x)).mp hxU
  have ha : a≠0 := by
    intro he
    have hxker : x∈π.ker := by
      change π x=1
      rw [←haimage,he,Matrix.SpecialLinearGroup.transvection_coeff_zero]
    exact hxQ (kernel_core x hxker)
  have hπx : π x=upper a := haimage.symm
  have hx : x*x=1 := by
    apply e.injective
    apply Subtype.ext
    simpa only [map_mul,map_one,Subgroup.coe_mul,Subgroup.coe_one,e,
      universalBOneActorEquiv,coveredActorEquiv_apply,pow_two] using
      ((mem_omegaCenterIn_iff _ _).mp
        ((source_Z_Q_U (reduced_triple h) (base (reducedFamily L S) (!i))).1 hxZ)).2.2
  obtain ⟨t,ht,htsq,ho,hπt,z,hz,hzker,g,hg⟩ := nat.exists_full_cartan_reflection H (cartan c)
    π honto hn (cartan_odd c) hcenter hsquare hdiag hfull b hb hb1 x hx a ha hπx
  have htri' (k : H) (hk : (k:A.Universal)∈Universal.cosetFamily A (!i)) :
      (π k).val 1 0=0 := by
    apply htri (e k)
    rw [RankTwo.stabilizer,stabilizer_base]
    change bOne_tree_map h k∈reducedFamily L S (!i)
    rw [←(bOne_tree_cover h).map_eq (!i)]
    exact mem_map_of_mem _ hk
  have hfix : (t:A.Universal) • base (Universal.cosetFamily A) i=base (Universal.cosetFamily A) i := by
    have he := t.property.2
    rwa [←stabilizer_base (F := Universal.cosetFamily A) (i := i)] at he
  refine ⟨t,t.property,hfix,?_,congrArg Subtype.val htsq,
    (Subgroup.orderOf_coe t).trans ho,ht,?_,?_⟩
  · intro he
    have htP : (t:A.Universal)∈Universal.cosetFamily A (!i) := by
      rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !i)]
      exact he
    have hh := htri' t htP
    rw [hπt,braid_matrix a ha] at hh
    exact inv_ne_zero ha hh
  · refine ⟨x,hxR,?_,z,?_,kernel_core z hzker,g,g.property,congrArg H.subtype hg⟩
    · rw [Subgroup.orderOf_coe]
      apply orderOf_eq_prime (show x^2=1 by simpa only [pow_two] using hx)
      intro he
      have hh := congrArg (fun z : SL(2,F) => z.val 0 1) hπx
      rw [he,map_one] at hh
      exact ha (by simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh.symm)
    · rw [centerIn_eq_map_center]
      exact mem_map_of_mem H.subtype hz
  · intro z hzK hzM
    apply nat.commutes_cartan_localKernel H (cartan c)
      (RankTwo.ballKernel (Universal.cosetFamily A) (base (Universal.cosetFamily A) i) 1)
      π honto hn _ (cartan_odd c) _ t ht z hzK hzM
    · intro k hk
      apply RankTwo.stabilizer_le_normalizer_ballKernel (Universal.cosetFamily A)
        (base (Universal.cosetFamily A) i) 1
      rw [RankTwo.stabilizer,stabilizer_base]
      exact hk.2
    · intro y hy
      apply htri' y
      have hadj : (sourceGraph A).Adj (base (Universal.cosetFamily A) i)
          (base (Universal.cosetFamily A) (!i)) :=
        ⟨by change i≠!i; cases i <;> decide,incident_base _ _ _⟩
      have he := (RankTwo.ballKernel_one_le_edge (Universal.cosetFamily A) hadj hy).2
      change (y:A.Universal)∈RankTwo.stabilizer (Universal.cosetFamily A)
        (base (Universal.cosetFamily A) (!i)) at he
      rwa [RankTwo.stabilizer,stabilizer_base] at he

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
