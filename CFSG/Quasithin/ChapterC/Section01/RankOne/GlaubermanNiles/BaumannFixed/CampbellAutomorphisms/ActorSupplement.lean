module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellAutomorphisms.FullActorConjugates
/-!
# The core-intersection and index step for a transported natural actor

A noncore Sylow element fixes precisely C_V(S). For an injective transported
actor X, submaximal control centralizes F on X∩O₂(H). If X moves F, some
image of F lies outside the core; its fixed points force X∩O₂(H) into the
fixed subgroup. A transport fixing that subgroup and taking X onto V
therefore gives XO₂(H)=S by the natural fixed-index bound.

The transport, submaximal placement and fixed-subgroup identities are
explicit here; the Sylow-automorphism source consumer constructs them.
Source: Campbell II.6.3, printed pp.30–31.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterC.GlaubermanNiles
variable {B H : Type*} [Group B] [Finite B] [Group H] [Finite H] {e : B →* H}

theorem InLocalClass.campbell_fixed_by_noncore_actor (h : InLocalClass e) (hB : IsBaumannFixed B)
    (t : H) (ht : t ∈ e.range) (htQ : t ∉ pCore 2 H) :
    Campbell.V H ⊓ centralizer ({t} : Set H) = Campbell.V H ⊓ centralizer (e.range : Set H) := by
  apply le_antisymm
  · intro v hv
    refine ⟨hv.1,?_⟩
    by_contra hn
    have hc := h.campbell_point_centralizer_eq_core hB v hv.1 hn
    apply htQ
    rw [←hc]
    exact ⟨ht,mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hv.2).symm⟩
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr ht))

theorem InLocalClass.campbell_natural_index_ge_sylow_index (h : InLocalClass e) (hB : IsBaumannFixed B) :
    (pCore 2 H).relIndex e.range ≤ (centralizer (e.range : Set H)).relIndex (Campbell.V H) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  obtain ⟨q,f,hq,hk,hf,he⟩ := h.exists_campbell_projection hB m
  let P := d.sylow.mapSurjective (f := q) hq
  have hSK : (d.sylow : Subgroup H) ⊓ q.ker = pCore 2 H := by
    rw [hk]
    exact d.sylow_inf_eq_core _ h.core_le_localKernel h.kernel_noPartialComplement
  have hKS : q.ker.subgroupOf (d.sylow : Subgroup H) = (pCore 2 H).subgroupOf (d.sylow : Subgroup H) := by
    ext s
    exact ⟨fun hs => hSK ▸ (show (s:H) ∈ (d.sylow:Subgroup H) ⊓ q.ker from ⟨s.property,hs⟩),
      fun hs => by rw [hk]; exact h.core_le_localKernel hs⟩
  have hi : (pCore 2 H).relIndex (d.sylow : Subgroup H) = Nat.card P := by
    change (pCore 2 H).relIndex (d.sylow : Subgroup H) = Nat.card ((d.sylow : Subgroup H).map q)
    rw [←relIndex_ker (d.sylow : Subgroup H) q]
    change ((pCore 2 H).subgroupOf (d.sylow : Subgroup H)).index =
      (q.ker.subgroupOf (d.sylow : Subgroup H)).index
    rw [hKS]
  have hPn : (P : Subgroup SL(2,F)) ≠ ⊥ := by
    intro hp
    have hSq : (d.sylow : Subgroup H) ≤ q.ker := (Subgroup.map_eq_bot_iff _).mp hp
    have hEQ : (d.sylow : Subgroup H)=pCore 2 H := (inf_eq_left.mpr hSq).symm.trans hSK
    obtain ⟨T,hT,hP⟩ := h.sylow
    apply (ChapterB.isMinimalParabolicOver_top_iff T).mp hP |>.2
    have ht : (T:Subgroup H)=pCore 2 H := hT.symm.trans (hS.symm.trans hEQ)
    rw [ht]
    infer_instance
  have hfixed := h.centralizer_moved_eq_natural_fixed_preimage hB m q hq hk f hf he (d.sylow : Subgroup H)
  rw [←hS,h.campbellV_eq_moved hB m,hi]
  change Nat.card P ≤ ((centralizer (d.sylow : Set H)).subgroupOf (moved e)).index
  change (centralizer (d.sylow : Set H)).subgroupOf (moved e) = _ at hfixed
  rw [hfixed,(Theory.SpecificGroups.SL2.NaturalFixedIndex.fixed ((d.sylow:Subgroup H).map q)).index_comap_of_surjective hf]
  exact Theory.SpecificGroups.SL2.NaturalFixedIndex.card_le_fixed_index hPn P.isPGroup'


theorem InLocalClass.transported_actor_core_le_fixed (h : InLocalClass e) (hB : IsBaumannFixed B)
    (W X A : Subgroup H) (f : W →* H) (hf : Function.Injective f)
    (hFr : Campbell.F H ≤ W) (hXr : X ≤ W) (hfS : f.range ≤ e.range)
    (hA : A ∈ elementaryAbelianMaxSubgroups e.range) (hXA : X ≤ A)
    (hfX : ∀ x : W, (x:H) ∈ X → f x ∈ Campbell.V H)
    (hZr : Campbell.V H ⊓ centralizer (e.range : Set H) ≤ W)
    (hfZ : ∀ z : W, (z:H) ∈ Campbell.V H ⊓ centralizer (e.range : Set H) → f z = (z:H))
    (hmove : ¬ Campbell.F H ≤ centralizer (X : Set H)) :
    X ⊓ pCore 2 H ≤ Campbell.V H ⊓ centralizer (e.range : Set H) := by
  obtain ⟨d,_,hS⟩ := h.exists_campbellEmbedding hB
  obtain ⟨n,hn,F,_,_,_,hcard,⟨m⟩⟩ := h.natural
  have hVC : Campbell.V H ≤ centralizer (pCore 2 H : Set H) :=
    Campbell.V_le_omegaCore.trans (fun x hx => ((mem_omegaOneCenterAmbient_iff _ x).mp hx).2.2)
  have hXC := (h.campbellF_submaximal_control hB m d X A (hS ▸ hA) hXA).1
  have hr : ∃ r : Campbell.F H, f ⟨r,hFr r.property⟩ ∉ pCore 2 H := by
    by_contra hn
    push Not at hn
    apply hmove
    intro r hr x hx
    let r' : W := ⟨r,hFr hr⟩
    let x' : W := ⟨x,hXr hx⟩
    have hcomm : f x' * f r' = f r' * f x' :=
      (hVC (hfX x' hx) (f r') (hn ⟨r,hr⟩)).symm
    have he : x'*r'=r'*x' := hf (by simpa only [map_mul] using hcomm)
    exact congrArg Subtype.val he
  obtain ⟨r,hr⟩ := hr
  let r' : W := ⟨r,hFr r.property⟩
  intro x hx
  let x' : W := ⟨x,hXr hx.1⟩
  have hcomm : f x' * f r' = f r' * f x' := by
    have he : x'*r'=r'*x' := Subtype.ext (hXC hx r r.property).symm
    simpa only [map_mul] using congrArg f he
  have hfx : f x' ∈ Campbell.V H ⊓ centralizer (e.range : Set H) := by
    rw [←h.campbell_fixed_by_noncore_actor hB (f r') (hfS ⟨r',rfl⟩) hr]
    exact ⟨hfX x' hx.1,mem_centralizer_singleton_iff.mpr hcomm⟩
  let z : W := ⟨f x',hZr hfx⟩
  have hxz : x'=z := hf (hfZ z hfx).symm
  have hxfx : x=f x' := congrArg Subtype.val hxz
  rwa [hxfx]


theorem InLocalClass.transported_actor_sup_core_eq_sylow (h : InLocalClass e) (hB : IsBaumannFixed B)
    (W X A : Subgroup H) (f : W →* H) (hf : Function.Injective f)
    (hFr : Campbell.F H ≤ W) (hXr : X ≤ W) (hXS : X ≤ e.range) (hfS : f.range ≤ e.range)
    (hA : A ∈ elementaryAbelianMaxSubgroups e.range) (hXA : X ≤ A)
    (hfX : (X.subgroupOf W).map f = Campbell.V H)
    (hZX : Campbell.V H ⊓ centralizer (e.range : Set H) ≤ X)
    (hfZ : ∀ z : W, (z:H) ∈ Campbell.V H ⊓ centralizer (e.range : Set H) → f z = (z:H))
    (hmove : ¬ Campbell.F H ≤ centralizer (X : Set H)) : X ⊔ pCore 2 H=e.range := by
  let Z := Campbell.V H ⊓ centralizer (e.range : Set H)
  have hZr : Z ≤ W := hZX.trans hXr
  have hZmap : (Z.subgroupOf W).map f=Z := by
    apply le_antisymm
    · rintro y ⟨z,hz,rfl⟩
      rw [hfZ z hz]
      exact hz
    · intro z hz
      exact ⟨⟨z,hZr hz⟩,hz,hfZ _ hz⟩
  have hXQ : X ⊓ pCore 2 H=Z := by
    apply le_antisymm
    · exact h.transported_actor_core_le_fixed hB W X A f hf hFr hXr hfS hA hXA
        (fun x hx => hfX ▸ mem_map_of_mem f hx) hZr hfZ hmove
    · exact le_inf hZX (inf_le_left.trans Campbell.V_le_pCore)
  have hm := relIndex_map_map_of_injective (Z.subgroupOf W) (X.subgroupOf W) hf
  rw [hZmap,hfX] at hm
  have hi := relIndex_map_map_of_injective (Z.subgroupOf W) (X.subgroupOf W) W.subtype_injective
  rw [map_subgroupOf_eq_of_le hZr,map_subgroupOf_eq_of_le hXr] at hi
  have hZXindex : Z.relIndex (Campbell.V H)=Z.relIndex X := hm.trans hi.symm
  have hXindex : (pCore 2 H).relIndex X=Z.relIndex (Campbell.V H) := by
    rw [←inf_relIndex_left X (pCore 2 H),hXQ,hZXindex]
  have hl := h.campbell_natural_index_ge_sylow_index hB
  have hZindex : Z.relIndex (Campbell.V H)=(centralizer (e.range:Set H)).relIndex (Campbell.V H) :=
    inf_relIndex_left _ _
  rw [←hZindex,←hXindex] at hl
  obtain ⟨T,hT,_⟩ := h.sylow
  have hQS : pCore 2 H ≤ e.range := hT ▸ pCore_isPGroup.le_sylow_of_normal T
  have hsupS : pCore 2 H ⊔ X ≤ e.range := sup_le hQS hXS
  have hmult := relIndex_mul_relIndex (pCore 2 H) (pCore 2 H ⊔ X) e.range le_sup_left hsupS
  rw [relIndex_sup_left] at hmult
  let : (pCore 2 H).IsFiniteRelIndex X := isFiniteRelIndex_of_finiteIndex
  let : (pCore 2 H ⊔ X).IsFiniteRelIndex e.range := isFiniteRelIndex_of_finiteIndex
  have hpos : 0<(pCore 2 H).relIndex X := Nat.pos_of_ne_zero relIndex_ne_zero
  have hone : (pCore 2 H ⊔ X).relIndex e.range=1 := by
    have hle : (pCore 2 H ⊔ X).relIndex e.range ≤ 1 := by nlinarith
    exact le_antisymm hle (Nat.one_le_iff_ne_zero.mpr relIndex_ne_zero)
  rw [sup_comm]
  exact le_antisymm hsupS (relIndex_eq_one.mp hone)
end CFSG.Quasithin.ChapterC.GlaubermanNiles
