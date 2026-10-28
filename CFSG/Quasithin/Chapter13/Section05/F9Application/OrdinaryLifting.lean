module

public import CFSG.Quasithin.Chapter13.Section05.PlaneGeometry.TwoBlocks.SourceContainment.Ordinary
public import CFSG.Quasithin.Chapter13.Section05.F9Application.SmallActions

/-!
# Original F.9(e) for the ordinary A₆ source branch

An order-four quadratic conjugate action has a two-dimensional displacement
plane. The invariant nondegenerate pairing proves that the reverse action
also has order four. Align both displacement planes with V₂ by actual
elements of L∩G₁; their product with the original conjugator lies in N_G(V₂).
The ordinary plane-actor closure then puts Vᵍ in L, whose literal action is
even. An even quadratic subgroup of the point core has order at most two,
contradicting the order-four assumption. Apply the existing small-action
lifting theorem to g and g⁻¹.

The final source consumer retains the ordinary quotient, earlier plane
noncentrality, and C_G(V₃) ≤ M∩N_G(V). It consumes all three original F.9(e)
commutator antecedents and proves both seed commutators trivial. It does
not require the global bad-plane containment in 13.5.6(2).
Source: Aschbacher--Smith, proof of 13.5.7, printed pp.917--918.
-/

@[expose] public section
open Subgroup BinaryPermutation Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem image_card (A:Subgroup G) (hA:A≤V) : Nat.card (image d A)=Nat.card A := by
  change Nat.card ((A.subgroupOf V).map d.coordinate.toMonoidHom)=Nat.card A
  rw [Subgroup.card_map_of_injective d.coordinate.injective]
  exact Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv

private theorem centralizer_image_le_perp (X:Subgroup G)
    (hX:X≤localModuleNormalizer (M:=M) (V:=V)) :
    image d (V⊓centralizer (X:Set G))≤form.orthogonal (image d ⁅V,X⁆) := by
  rintro w ⟨v,hv,rfl⟩ y hy
  rw [image_commutator_self d X hX] at hy
  change form y (d.coordinate v).toAdd=0
  refine Submodule.span_induction (p:=fun y _=>form y (d.coordinate v).toAdd=0)
    ?_ ?_ ?_ ?_ hy
  · rintro y ⟨a,⟨x,rfl⟩,u,_,rfl⟩
    have hf:naturalRepresentation (Fin 6) (permutation d (inclusion hX x))
        (d.coordinate v).toAdd=(d.coordinate v).toAdd := by
      rw [←conjugation d]
      apply congrArg (fun v:V=>(d.coordinate v).toAdd)
      apply Subtype.ext
      change x.val*v.val*x.val⁻¹=v.val
      have he:x.val*v.val=v.val*x.val:=hv.2 x.val x.property
      rw [he,mul_inv_cancel_right]
    have hi:=form_invariant (permutation d (inclusion hX x)) u (d.coordinate v).toAdd
    rw [hf] at hi
    change form (naturalRepresentation (Fin 6) (permutation d (inclusion hX x)) u-u)
      (d.coordinate v).toAdd=0
    rw [map_sub,LinearMap.sub_apply,hi,sub_self]
  · simp
  · intro x y _ _ hx hy
    simp only [map_add,LinearMap.add_apply,hx,hy,add_zero]
  · intro a y _ hy
    simp only [map_smul,LinearMap.smul_apply,hy,smul_zero]

theorem conjugate_four_reverse_index (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hcard:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=4) :
    (centralizer (V.map (MulAut.conj g).toMonoidHom:Set G)).relIndex V=4 := by
  let X:=V.map (MulAut.conj g).toMonoidHom
  let C:=V⊓centralizer (X:Set G)
  obtain ⟨a,_,ha⟩:=conjugate_commutator_four_plane d g hg hc hcomm hs hcard
  have hd:finrank (ZMod 2) (image d ⁅V,X⁆)=2:=by
    rw [ha]
    exact (move_finrank a.val canonicalPlane).trans canonicalPlane_finrank
  have hCdim:finrank (ZMod 2) (image d C)=2:=by
    have hu:=Submodule.finrank_mono (centralizer_image_le_perp d X (conjugate_le_local d g hg hc hs))
    rw [LinearMap.BilinForm.finrank_orthogonal form_nondegenerate,
      finrank_natural_even (Fin 6) (by decide),hd] at hu
    norm_num at hu
    change finrank (ZMod 2) (image d C)≤2 at hu
    have he:IsMulCommutative X:=by
      let := elementary d
      exact inferInstanceAs (IsMulCommutative (V.map (MulAut.conj g).toMonoidHom))
    have hWC:⁅V,X⁆≤C:=le_inf (hcomm.trans inf_le_left)
      ((hcomm.trans inf_le_right).trans (le_centralizer_iff_isMulCommutative.mpr he))
    have hl:image d ⁅V,X⁆≤ image d C:=by
      rintro w ⟨v,hv,rfl⟩;exact ⟨v,hWC hv,rfl⟩
    have hd':=Submodule.finrank_mono hl
    rw [hd] at hd'
    omega
  have hCc:Nat.card C=4:=by
    rw [←image_card d C inf_le_left,Module.natCard_eq_pow_finrank (K:=ZMod 2),
      Nat.card_eq_fintype_card,ZMod.card,hCdim]
    norm_num
  have hVc:Nat.card V=16:=by
    rw [←image_card d V le_rfl,image_self d,Module.natCard_eq_pow_finrank (K:=ZMod 2),
      Nat.card_eq_fintype_card,ZMod.card,finrank_top,finrank_natural_even (Fin 6) (by decide)]
    norm_num
  have hh:=(C.subgroupOf V).card_mul_index
  have hec:Nat.card (C.subgroupOf V)=Nat.card C:=Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hec,hCc,hVc] at hh
  have hi:(C.subgroupOf V).index=(centralizer (X:Set G)).relIndex V:=
    inf_relIndex_left V (centralizer (X:Set G))
  rw [hi] at hh
  change (centralizer (X:Set G)).relIndex V=4
  omega

omit d [Finite G] in
private theorem centralizer_map_equiv_four (A:Subgroup G) (e:G≃*G) :
    (centralizer (A:Set G)).map e.toMonoidHom=centralizer (A.map e.toMonoidHom:Set G) := by
  ext g
  rw [mem_map_equiv]
  constructor
  · intro hg a ha
    obtain ⟨b,hb,rfl⟩:=ha
    have hh:=congrArg e (hg b hb)
    change e b*g=g*e b
    simpa only [map_mul,e.apply_symm_apply] using hh
  · intro hg a ha
    apply e.injective
    simpa only [map_mul,e.apply_symm_apply] using hg (e a) (mem_map_of_mem _ ha)

theorem conjugate_action_inverse_four (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hsecond:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁)
    (hcard:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=4) :
    Nat.card (conjugateAction d g⁻¹ (conjugate_le_local d g⁻¹ (G₁.inv_mem hg) hc
      (inverse_seed_commutator_le_line d g hg hsecond))).range=4 := by
  have he:(V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom=V:=by
    change (V.conjBy g⁻¹).conjBy g=V
    exact conjBy_inv' V g
  have ht:=relIndex_map_map_of_injective (f:=(MulAut.conj g).toMonoidHom)
    (centralizer (V:Set G)) (V.map (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g).injective
  rw [centralizer_map_equiv_four,he] at ht
  unfold conjugateAction
  rw [permutation_range_card d _ _,←ht]
  exact conjugate_four_reverse_index d g hg hc hcomm hs hcard

omit d [Finite G] in
theorem inverse_commutator_bound (g:G)
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom) :
    ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆≤V⊓V.map (MulAut.conj g⁻¹).toMonoidHom := by
  have hh:=map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hcomm
  rw [map_commutator,Subgroup.map_inf _ _ _ (MulAut.conj g⁻¹).injective] at hh
  change ⁅V.conjBy g⁻¹,(V.conjBy g).conjBy g⁻¹⁆≤V.conjBy g⁻¹⊓(V.conjBy g).conjBy g⁻¹ at hh
  rwa [conjBy_inv,commutator_comm,inf_comm] at hh

theorem conjugate_four_double_alignment (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hsecond:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁)
    (hcard:Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range=4) :
    ∃l∈L⊓G₁,∃k∈L⊓G₁,l*g*k⁻¹∈normalizer (V₂:Set G) := by
  obtain ⟨l,hl,hel⟩:=conjugate_commutator_four_alignment d g hg hc hcomm hs hcard
  obtain ⟨k,hk,hek⟩:=conjugate_commutator_four_alignment d g⁻¹ (G₁.inv_mem hg) hc
    (inverse_commutator_bound g hcomm) (inverse_seed_commutator_le_line d g hg hsecond)
    (conjugate_action_inverse_four d g hg hc hcomm hs hsecond hcard)
  refine ⟨l,hl,k,hk,?_⟩
  apply (normalizer (V₂:Set G)).inv_mem_iff.mp
  apply mem_normalizer_iff_map_conj_eq.mpr
  have hW:(⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj g⁻¹).toMonoidHom=
      ⁅V,V.map (MulAut.conj g⁻¹).toMonoidHom⁆:=by
    rw [map_commutator]
    change ⁅V.conjBy g⁻¹,(V.conjBy g).conjBy g⁻¹⁆=⁅V,V.conjBy g⁻¹⁆
    rw [conjBy_inv,commutator_comm]
  have he:(MulAut.conj (l*g*k⁻¹)⁻¹).toMonoidHom.comp (MulAut.conj l).toMonoidHom=
      (MulAut.conj k).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom:=by
    ext x:1
    change (l*g*k⁻¹)⁻¹*(l*x*l⁻¹)*((l*g*k⁻¹)⁻¹)⁻¹=k*(g⁻¹*x*(g⁻¹)⁻¹)*k⁻¹
    group
  calc
    _ = ((⁅V,V.map (MulAut.conj g).toMonoidHom⁆).map (MulAut.conj l).toMonoidHom).map
        (MulAut.conj (l*g*k⁻¹)⁻¹).toMonoidHom := congrArg (fun A:Subgroup G=>
          A.map (MulAut.conj (l*g*k⁻¹)⁻¹).toMonoidHom) hel.symm
    _ = _ := by rw [map_map,he,←map_map,hW,hek]

end CFSG.Quasithin.Chapter13.Section05.QuadraticSource

@[expose] public section
open Subgroup BinaryPermutation Module
namespace CFSG.Quasithin.Chapter13.Section05.QuadraticSource
open Section08.SourceCompletion Section07.NaturalAction PlaneGeometry.TwoBlocks
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open NaturalGeometry NaturalPairing
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G}
  {L V V₁ V₂ V₃ M G₁:Subgroup G}
  (d:NaturalSetup T L V V₁ V₂ V₃ M G₁)
include d

private theorem conjugate_le_local_component_of_double_alignment
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥)
    (g l k:G) (hl:l∈L) (hk:k∈L) (hh:l*g*k⁻¹∈normalizer (V₂:Set G)) :
    V.map (MulAut.conj g).toMonoidHom≤L := by
  let h:=l*g*k⁻¹
  have hVL:V.map (MulAut.conj h).toMonoidHom≤L:=by
    have hv:V.map (MulAut.conj h).toMonoidHom≤conjugateSpanBy V (normalizer (V₂:Set G)):=by
      rintro _ ⟨v,hv,rfl⟩
      exact (mem_normalizer_iff.mp (le_normalizer_conjugateSpanBy V _ hh) v).mp
        (le_conjugateSpanBy _ _ hv)
    exact hv.trans ((Ordinary.source_plane_closure_le_actor_core d e hm).trans
      ((pCoreIn_le 2 _).trans (planeActor_le.trans inf_le_left)))
  rintro _ ⟨v,hv,rfl⟩
  have hw:k*v*k⁻¹∈V:=(mem_normalizer_iff.mp (d.normalizes_V (mem_sup_left hk)) v).mp hv
  have hz:h*(k*v*k⁻¹)*h⁻¹∈L:=hVL ⟨_,hw,rfl⟩
  have hmem:=L.mul_mem (L.mul_mem (L.inv_mem hl) hz) hl
  convert hmem using 1
  dsimp [h]
  group

omit d in
private theorem even_conjugate_core_bound (A:Subgroup (Equiv.Perm (Fin 6)))
    (a:Equiv.Perm (Fin 6))
    (hcore:A≤pointCore.map (MulAut.conj a).toMonoidHom)
    (hq:QuadraticPointCore.Quadratic A) (he:A≤alternatingGroup (Fin 6)) : Nat.card A≤2 := by
  let B:=A.map (MulAut.conj a⁻¹).toMonoidHom
  have hB:B≤pointCoreEven:=by
    rintro _ ⟨x,hx,rfl⟩
    constructor
    · obtain ⟨y,hy,hey⟩:=hcore hx
      rw [←hey]
      change a⁻¹*(a*y*a⁻¹)*a∈pointCore
      have he:a⁻¹*(a*y*a⁻¹)*a=y:=by group
      rw [he]
      exact hy
    · have hh:=map_mono (f:=(MulAut.conj a⁻¹).toMonoidHom) he
      rw [conjugate_alternating] at hh
      exact hh (mem_map_of_mem _ hx)
  have hb:=QuadraticPointCore.even_quadratic_card_le_two B hB
    (QuadraticPointCore.quadratic_conjugate A hq a⁻¹)
  rwa [card_map_of_injective (MulAut.conj a⁻¹).injective] at hb

theorem ordinary_source_small_action
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥)
    (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hsecond:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁) :
    Nat.card (conjugateAction d g (conjugate_le_local d g hg hc hs)).range≤2 := by
  let f:=conjugateAction d g (conjugate_le_local d g hg hc hs)
  have hbound:Nat.card f.range≤4:=conjugate_action_card_le_four d g hg hc hcomm hs
  change Nat.card f.range≤2
  by_contra hsmall
  have hp:IsPGroup 2 f.range:=by
    let := elementary d
    exact ((IsElementaryAbelian.isPGroup 2 V).map (MulAut.conj g).toMonoidHom).of_surjective
      f.rangeRestrict f.rangeRestrict_surjective
  have h4:Nat.card f.range=4:=by
    rcases hp.card_eq_or_dvd with h1|h2
    · exact (hsmall (by omega)).elim
    · omega
  obtain ⟨l,hl,k,hk,hh⟩:=conjugate_four_double_alignment d g hg hc hcomm hs hsecond h4
  have hVL:=conjugate_le_local_component_of_double_alignment d e hm g l k hl.1 hk.1 hh
  have hev:f.range≤alternatingGroup (Fin 6):=by
    rintro _ ⟨x,rfl⟩
    let l:L:=⟨x.val,hVL x.property⟩
    have hmem:localMap d l∈alternatingGroup (Fin 6):=(localMap_range d).le ⟨l,rfl⟩
    rw [localMap_eq_full d l] at hmem
    exact hmem
  obtain ⟨a,_,ha⟩:=conjugate_pointCore_placement d g hg hc hs
  exact hsmall (even_conjugate_core_bound f.range a.val ha
    (conjugate_quadratic_source d g hg hc hcomm hs) hev)

theorem ordinary_source_commutator_lifting
    (e:(L⧸pCore 2 L)≃*alternatingGroup (Fin 6))
    (hm:⁅(normalizer (V₁:Set G)).pCoreIn 2,V₂⁆≠⊥)
    (g:G) (hg:g∈G₁)
    (hc:centralizer (V₃:Set G)≤localModuleNormalizer (M:=M) (V:=V))
    (hcomm:⁅V,V.map (MulAut.conj g).toMonoidHom⁆≤V⊓V.map (MulAut.conj g).toMonoidHom)
    (hs:⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆≤V₁)
    (hsecond:⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆≤V₁) :
    ⁅V₃,V.map (MulAut.conj g).toMonoidHom⁆=⊥ ∧
      ⁅V₃.map (MulAut.conj g).toMonoidHom,V⁆=⊥ := by
  apply source_lifting_of_small_actions d g hg hc hcomm hs hsecond
  · exact ordinary_source_small_action d e hm g hg hc hcomm hs hsecond
  · have hsi:⁅V₃.map (MulAut.conj g⁻¹).toMonoidHom,V⁆≤V₁:=by
      have hh:=map_mono (f:=(MulAut.conj g⁻¹).toMonoidHom) hs
      rw [map_commutator] at hh
      change ⁅V₃.conjBy g⁻¹,(V.conjBy g).conjBy g⁻¹⁆≤V₁.conjBy g⁻¹ at hh
      rw [conjBy_inv] at hh
      have he:V₁.conjBy g⁻¹=V₁:=mem_normalizer_iff_map_conj_eq.mp
        (d.first_normalizer ▸ G₁.inv_mem hg)
      rwa [he] at hh
    exact ordinary_source_small_action d e hm g⁻¹ (G₁.inv_mem hg) hc
      (inverse_commutator_bound g hcomm) (inverse_seed_commutator_le_line d g hg hsecond) hsi

end CFSG.Quasithin.Chapter13.Section05.QuadraticSource
