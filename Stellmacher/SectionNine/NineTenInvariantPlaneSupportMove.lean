module
public import Stellmacher.SectionNine.NineFiveCanonicalPair
public import Stellmacher.SectionOne.OneSevenInvariantFourDisplacement
public import Stellmacher.SectionOne.OneSevenTwoGroupSupportMove

/-!
# Nontrivial action on the invariant plane exchanges the canonical supports

In the actual faithful one-seven action on an elementary group of order
sixteen, let S be a two-subgroup of order greater than four containing a
rank-one actor in a chosen canonical factor. If a supplied element of S
acts nontrivially on an S-invariant plane of order four, it exchanges the
chosen support with its complementary canonical support.

An S-element exchanges the supports by the two-group support theorem.
The invariant-four displacement theorem puts the rank-one line in the
plane, as well as its exchanged line. They are disjoint and exhaust that
plane. Its intersections with the two supports therefore have order two.
An actor preserving both supports preserves and fixes each intersection,
so fixes the entire plane. The canonical pair permutation theorem forces
the supplied nontrivial actor to exchange the supports instead.

This detects a moving actor in the normal core-intersection image used
after Stellmacher (9.10)(10), printed pp.58–59. Together with the normal
subgroup displacement bound it proves the needed order-eight displacement
without assuming the stronger source edge-generation assertion.
-/

namespace Stellmacher.SectionNine
open SectionOne
open scoped IsMulCommutative
universe u

private theorem fixes_split_plane
    {W : Type u} [Group W] [Finite W] [IsMulCommutative W]
    (U V I L M : Subgroup W) (hUV : Disjoint U V)
    (hI : Nat.card I = 4) (hL : Nat.card L = 2) (hM : Nat.card M = 2)
    (hLI : L ≤ I) (hLU : L ≤ U) (hMI : M ≤ I) (hMV : M ≤ V)
    (g : MulAut W) (hgI : I.map g.toMonoidHom = I)
    (hgU : U.map g.toMonoidHom = U) (hgV : V.map g.toMonoidHom = V) :
    ∀ point ∈ I, g point = point := by
  have hLM : Disjoint L M := hUV.mono hLU hMV
  have hcard := Subgroup.card_sup_eq_mul_of_normalizes_of_disjoint L M
    (by rw [Subgroup.normalizer_eq_top]; exact le_top) hLM
  have hjoin : L ⊔ M = I := Subgroup.eq_of_le_of_card_ge (sup_le hLI hMI)
    (by rw [hcard,hL,hM,hI])
  have hleft : I ⊓ U = L := by
    apply le_antisymm ?_ (le_inf hLI hLU)
    rintro x ⟨hxI,hxU⟩
    rw [←hjoin] at hxI
    let _ : L.Normal := Subgroup.normal_of_isMulCommutative L
    obtain ⟨l,hl,m,hm,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxI
    have hmU : m ∈ U := by
      have hh := U.mul_mem (U.inv_mem (hLU hl)) hxU
      simpa only [inv_mul_cancel_left] using hh
    have hmOne : m=1 := hUV.le_bot ⟨hmU,hMV hm⟩
    simpa only [hmOne,mul_one] using hl
  have hright : I ⊓ V = M := by
    apply le_antisymm ?_ (le_inf hMI hMV)
    rintro x ⟨hxI,hxV⟩
    rw [←hjoin] at hxI
    let _ : L.Normal := Subgroup.normal_of_isMulCommutative L
    obtain ⟨l,hl,m,hm,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxI
    have hlV : l ∈ V := by
      have hh := V.mul_mem hxV (V.inv_mem (hMV hm))
      simpa only [mul_inv_cancel_right] using hh
    have hlOne : l=1 := hUV.le_bot ⟨hLU hl,hlV⟩
    simpa only [hlOne,one_mul] using hm
  have fixLine (J : Subgroup W) (hJ : Nat.card J=2)
      (hgJ : J.map g.toMonoidHom=J) : ∀ point∈J, g point=point := by
    obtain ⟨other,hother,hunique⟩ := (Nat.card_eq_two_iff' (1:J)).mp hJ
    intro point hpoint
    by_cases hone : point=1
    · rw [hone,map_one]
    · have hgpoint : g point∈J := hgJ.le (Subgroup.mem_map_of_mem g.toMonoidHom hpoint)
      have hgne : g point≠1 := fun h => hone (g.injective (h.trans (map_one g).symm))
      exact congrArg Subtype.val ((hunique ⟨g point,hgpoint⟩
        (fun h => hgne (congrArg Subtype.val h))).trans
          (hunique ⟨point,hpoint⟩ (fun h => hone (congrArg Subtype.val h))).symm)
  have hfixL : ∀ point∈L,g point=point := fixLine L hL (by
    rw [←hleft,Subgroup.map_inf _ _ _ g.injective,hgI,hgU])
  have hfixM : ∀ point∈M,g point=point := fixLine M hM (by
    rw [←hright,Subgroup.map_inf _ _ _ g.injective,hgI,hgV])
  intro point hpoint
  rw [←hjoin] at hpoint
  let _ : L.Normal := Subgroup.normal_of_isMulCommutative L
  obtain ⟨l,hl,m,hm,rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hpoint
  rw [map_mul,hfixL l hl,hfixM m hm]

public theorem nine_ten_invariant_plane_actor_moves_support
    {W : Type u} [Group W] [Finite W] [IsElementaryAbelian 2 W]
    (X : Subgroup (MulAut W)) (hyp : Hypotheses X W)
    (D S : Subgroup X) (hD : IsOneSevenFactor (V:=W) D)
    (hS : IsPGroup 2 S) (hW : Nat.card W=16) (hlarge : 4<Nat.card S)
    (a : X) (haD : a∈D) (haS : a∈S)
    (hrank : Nat.card (commutatorAction (Subgroup.zpowers (a:MulAut W)) W)=2)
    (I : Subgroup W) (hI : Nat.card I=4)
    (hInv : ∀ s∈S, I.map (s:MulAut W).toMonoidHom=I)
    (c : X) (hc : c∈S) (hnontrivial : ∃ point∈I, (c:MulAut W) point≠point) :
    commutatorAction D W ≠ (commutatorAction D W).map (c:MulAut W).toMonoidHom ∧
      commutatorAction D W ⊔ (commutatorAction D W).map (c:MulAut W).toMonoidHom=⊤ := by
  obtain ⟨b,hmove,hspan⟩ := oneSevenFactor_exists_complementary_two_group_conjugate
    hyp D S hD hS hW hlarge
  let E := D.conjBy (b:X)
  let U := commutatorAction D W
  let V := commutatorAction E W
  change U ≠ U.map ((b:X):MulAut W).toMonoidHom at hmove
  change U ⊔ U.map ((b:X):MulAut W).toMonoidHom = ⊤ at hspan
  have hE := hD.conjBy D (b:X)
  have hVmap : U.map ((b:X):MulAut W).toMonoidHom=V :=
    RankOneThreeGroupAssembly.commutatorAction_conjBy D (b:X)
  have hDE : D≠E := by
    intro heq
    apply hmove
    rw [hVmap,show V=U from congrArg (fun F:Subgroup X => commutatorAction F W) heq.symm]
  have hUV : Disjoint U V := oneSevenFactor_support_disjoint_of_ne hyp D E hD hE hDE
  have hUVspan : U⊔V=⊤ := by rwa [hVmap] at hspan
  have hpair := nine_five_canonical_pair_of_support_span hyp D E hD hE hDE hUVspan
  let L := commutatorAction (Subgroup.zpowers (a:MulAut W)) W
  let M := L.map ((b:X):MulAut W).toMonoidHom
  have hLI : L≤I := oneSevenFactor_displacement_le_invariant_four X hyp D hD a b
    haD hrank hmove hspan I hI
      (fun point hpoint => (hInv a haS).le (Subgroup.mem_map_of_mem _ hpoint))
      (hInv b b.property)
  have hLU : L≤U := by
    have hcyclic : L=commutatorAction (Subgroup.zpowers a) W := by
      rw [←commutatorAction_map_actor_subtype X (Subgroup.zpowers a),MonoidHom.map_zpowers]
      rfl
    rw [hcyclic]
    change commutatorAction (Subgroup.zpowers a) W ≤ commutatorAction D W
    rw [commutatorAction_eq_closure,commutatorAction_eq_closure]
    apply Subgroup.closure_mono
    rintro point ⟨mover,vector,rfl⟩
    exact ⟨⟨mover,(Subgroup.zpowers_le.mpr haD) mover.property⟩,vector,rfl⟩
  have hMI : M≤I := (Subgroup.map_mono hLI).trans_eq (hInv b b.property)
  have hMV : M≤V := (Subgroup.map_mono hLU).trans_eq hVmap
  have hMcard : Nat.card M=2 := (Subgroup.card_map_of_injective
    ((b:X):MulAut W).injective).trans hrank
  rcases hpair.2.2.2.1 c with ⟨hDc,hEc⟩ | ⟨hDc,hEc⟩
  · have hUc : U.map (c:MulAut W).toMonoidHom=U := by
      exact (RankOneThreeGroupAssembly.commutatorAction_conjBy D c).trans
        (congrArg (fun F:Subgroup X => commutatorAction F W) hDc)
    have hVc : V.map (c:MulAut W).toMonoidHom=V := by
      exact (RankOneThreeGroupAssembly.commutatorAction_conjBy E c).trans
        (congrArg (fun F:Subgroup X => commutatorAction F W) hEc)
    obtain ⟨point,hpoint,hnot⟩ := hnontrivial
    exact (hnot (fixes_split_plane U V I L M hUV hI hrank hMcard
      hLI hLU hMI hMV c (hInv c hc) hUc hVc point hpoint)).elim
  · have hUc : U.map (c:MulAut W).toMonoidHom=V := by
      exact (RankOneThreeGroupAssembly.commutatorAction_conjBy D c).trans
        (congrArg (fun F:Subgroup X => commutatorAction F W) hDc)
    have hUne : U≠V := by
      intro heq
      have hbot := hUV.eq_bot
      rw [heq,inf_idem] at hbot
      have hh := congrArg (fun F:Subgroup W => Nat.card F) hbot
      rw [hE.2.2.1,Subgroup.card_bot] at hh
      omega
    exact ⟨by change U≠U.map (c:MulAut W).toMonoidHom; rwa [hUc],by
      change U⊔U.map (c:MulAut W).toMonoidHom=⊤
      rwa [hUc]⟩

end Stellmacher.SectionNine
