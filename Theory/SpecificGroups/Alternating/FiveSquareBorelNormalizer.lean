module
public import Theory.Alternating.FivePairBorelTorus
public import Theory.GroupTheory.SolvableSylowControl
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# Borel normalizers above a normal A₅ square

In an extension of order 28800, the normalizer of a Sylow subgroup of the
normal A₅ square has order 1152, by the Frattini argument and the intrinsic
order 144 of its Borel. A solvable Sylow overgroup with two-core quotient
of order 72 therefore fills this normalizer, and its two-core is exactly
the square's Sylow subgroup. Normality of the square gives weak closure.
Both conclusions lift through an arbitrary two-group kernel, preserving
the given subgroup, its own two-core, and the conjugating element.

The literal S₅ wreath model supplies the required normal square through
its actual inner automorphism subgroup. The Chapter14 four-element-field
consumer discharges solvable Sylow control and applies this to Mc/O₂(Mc).

Source application: Aschbacher--Smith 14.6.14(3), 14.6.16, pp.1033,1035.
-/

public section
open Subgroup Theory.GroupTheory
namespace Theory.AlternatingFive
variable {G : Type*} [Group G] [Finite G]
local notation "A5" => alternatingGroup (Fin 5)

private theorem pair_card : Nat.card (A5 × A5) = 3600 := by
  rw [Nat.card_prod,nat_card_alternatingGroup,Nat.card_fin]
  norm_num [Nat.factorial]

private theorem pair_sylow_card (S : Sylow 2 (A5 × A5)) : Nat.card S = 16 := by
  rw [S.card_eq_multiplicity,pair_card]
  decide +kernel

/-- The normalizer of a Sylow of the normal A₅ square in an order-28800
extension has order 1152. -/
theorem square_sylow_normalizer_card (N : Subgroup G) [N.Normal]
    (e : N ≃* A5 × A5) (hc : Nat.card G = 28800) (P : Sylow 2 N) :
    Nat.card (normalizer ((P : Subgroup N).map N.subtype : Set G)) = 1152 := by
  let U := (P : Subgroup N).map N.subtype
  let J := normalizer (U : Set G)
  have hN : Nat.card N = 3600 := (Nat.card_congr e.toEquiv).trans pair_card
  have hi : N.index = 8 := by
    have hh := N.card_mul_index
    rw [hN,hc] at hh
    omega
  have hsup : J ⊔ N = ⊤ := P.normalizer_sup_eq_top
  have hrel : N.relIndex J = 8 := by
    rw [←relIndex_sup_right J N,hsup,relIndex_top_right,hi]
  have hPN : U.subgroupOf N = (P : Subgroup N) :=
    comap_map_eq_self_of_injective N.subtype_injective _
  have heq : J.subgroupOf N = normalizer (P : Set N) := by
    rw [subgroupOf_normalizer_eq (map_subtype_le _),hPN]
    rfl
  have hcard : Nat.card (J.subgroupOf N) = 144 := by
    rw [heq,←card_map_of_injective (f := e.toMonoidHom) e.injective]
    change Nat.card ((normalizer ((P : Subgroup N) : Set N)).map e.toMonoidHom) = _
    rw [map_equiv_normalizer_eq]
    exact pair_sylow_normalizer_card (P.mapSurjective e.surjective)
  have hcomm : Nat.card (N.subgroupOf J) = Nat.card (J.subgroupOf N) := by
    exact Nat.card_congr {
      toFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
      invFun := fun x => ⟨⟨x.val.val,x.property⟩,x.val.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hh := (N.subgroupOf J).card_mul_index
  change Nat.card (N.subgroupOf J) * N.relIndex J = Nat.card J at hh
  rw [hcomm,hcard,hrel] at hh
  exact hh.symm

/-- A solvable Sylow overgroup with two-core quotient of order 72 is exactly
the normalizer of the square's Sylow. Its own two-core is that same Sylow. -/
theorem square_solvable_overgroup (N B : Subgroup G) [N.Normal]
    (e : N ≃* A5 × A5) (hc : Nat.card G = 28800)
    (hcontrol : SolvableSylowControl 2 N)
    (T : Sylow 2 G) (hTB : (T : Subgroup G) ≤ B)
    (hB : Group.IsSolvable B) (hb : Nat.card (B ⧸ pCore 2 B) = 72) :
    B = normalizer (((T : Subgroup G) ⊓ N : Subgroup G) : Set G) ∧
      B.pCoreIn 2 = (T : Subgroup G) ⊓ N := by
  obtain ⟨P,hP⟩ := T.exists_subgroupOf_eq_of_normal N
  let U := (P : Subgroup N).map N.subtype
  have hU : U = (T : Subgroup G) ⊓ N := by
    change ((P : Subgroup N).map N.subtype) = _
    rw [hP,subgroupOf_map_subtype]
  have hUB : U ≤ B := hU ▸ inf_le_left.trans hTB
  let := hB
  have hn : B ≤ normalizer (U : Set G) := hcontrol.normalizes_sylow N B P
    (by simp [normalizer_eq_top]) hUB
  have hp : U ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (P.isPGroup'.map N.subtype) hUB hn
  have hPc : Nat.card U = 16 := by
    change Nat.card ((P : Subgroup N).map N.subtype) = _
    rw [card_map_of_injective N.subtype_injective]
    have hh := pair_sylow_card (P.mapSurjective (f := e.toMonoidHom) e.surjective)
    change Nat.card ((P : Subgroup N).map e.toMonoidHom) = 16 at hh
    rwa [card_map_of_injective e.injective] at hh
  have hcore : 16 ≤ Nat.card (pCore 2 B) := by
    have hh := card_le_of_le hp
    simpa only [hPc,pCoreIn,card_map_of_injective B.subtype_injective] using hh
  have hBc : Nat.card B = Nat.card (pCore 2 B) * 72 := by
    rw [←(pCore 2 B).card_mul_index,index_eq_card,hb]
  have hNc := square_sylow_normalizer_card N e hc P
  have hEq : B = normalizer (U : Set G) := by
    apply eq_of_le_of_card_ge hn
    rw [hNc,hBc]
    omega
  have hcorec : Nat.card (pCore 2 B) = 16 := by
    have hh : Nat.card B = 1152 := hEq ▸ hNc
    omega
  have hcoreeq : U = B.pCoreIn 2 := by
    apply eq_of_le_of_card_ge hp
    simp only [pCoreIn,card_map_of_injective B.subtype_injective,hcorec,hPc,le_refl]
  exact ⟨hU ▸ hEq,hU ▸ hcoreeq.symm⟩

/-- A Sylow intersection with a normal subgroup is weakly closed in the same
ambient Sylow. This retains the actual conjugator. -/
theorem normal_intersection_weakly_closed (N : Subgroup G) [N.Normal]
    (T : Sylow 2 G) (g : G)
    (hg : ((T : Subgroup G) ⊓ N).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G)) :
    ((T : Subgroup G) ⊓ N).map (MulAut.conj g).toMonoidHom = (T : Subgroup G) ⊓ N := by
  apply eq_of_le_of_card_ge
  · apply le_inf hg
    have hn := map_mono (f := (MulAut.conj g).toMonoidHom)
      (inf_le_right : (T : Subgroup G) ⊓ N ≤ N)
    have he : N.map (MulAut.conj g).toMonoidHom = N :=
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (N : Set G) by
        simp only [normalizer_eq_top,mem_top])
    rwa [he] at hn
  · rw [card_map_of_injective (MulAut.conj g).injective]

end Theory.AlternatingFive

namespace Theory.AlternatingFive
open Subgroup Theory.GroupTheory
variable {G Q : Type*} [Group G] [Finite G] [Group Q] [Finite Q]
local notation "A5" => alternatingGroup (Fin 5)

/-- The same Borel normalizer and weak closure lift through a two-group
kernel. The subgroup and its two-core are the original ones upstairs. -/
theorem square_cover_solvable_overgroup
    (f : G →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (N : Subgroup Q) [N.Normal] (e : N ≃* A5 × A5)
    (hc : Nat.card Q = 28800) (hcontrol : SolvableSylowControl 2 N)
    (T : Sylow 2 G) (B : Subgroup G) (hTB : (T : Subgroup G) ≤ B)
    (hB : Group.IsSolvable B) (hb : Nat.card (B ⧸ pCore 2 B) = 72) :
    normalizer (B.pCoreIn 2 : Set G) = B ∧
      ∀ g : G, (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup G) →
        (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom = B.pCoreIn 2 := by
  let Tbar := T.mapSurjective hf
  let Bbar := B.map f
  let := hB
  have hs : Group.IsSolvable Bbar := Group.isSolvable_of_surjective (f.subgroupMap_surjective B)
  have hker : IsPGroup 2 (f.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let eb := (f.subgroupMap B).pCoreQuotientEquiv (f.subgroupMap_surjective B) hker
  have hbbar : Nat.card (Bbar ⧸ pCore 2 Bbar) = 72 := by
    rw [←Nat.card_congr eb.toEquiv]
    exact hb
  obtain ⟨hBn,hBc⟩ := square_solvable_overgroup N Bbar e hc hcontrol Tbar
    (map_mono hTB) hs hbbar
  have hkerB : f.ker ≤ B := (hk.le_sylow_of_normal T).trans hTB
  have hkerC : f.ker ≤ B.pCoreIn 2 := le_pCoreIn_of_normalizes hk hkerB
    (by simp [normalizer_eq_top])
  have hmap : (B.pCoreIn 2).map f = (Tbar : Subgroup Q) ⊓ N :=
    (map_pCoreIn_of_ker_isPGroup f hk B).trans hBc
  have hnorm : normalizer ((B.pCoreIn 2).map f : Set Q) = Bbar := by
    rw [hmap]
    exact hBn.symm
  have hnormalizer : normalizer (B.pCoreIn 2 : Set G) = B := by
    have hh := congrArg (comap f) hnorm
    rw [comap_normalizer_eq_of_surjective _ hf,comap_map_eq_self hkerC,
      comap_map_eq_self hkerB] at hh
    exact hh
  refine ⟨hnormalizer,?_⟩
  intro g hg
  have hconj (A : Subgroup G) :
      (A.map (MulAut.conj g).toMonoidHom).map f =
        (A.map f).map (MulAut.conj (f g)).toMonoidHom := by
    rw [map_map,map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply,MulEquiv.toMonoidHom_eq_coe,MulAut.conj_apply,
      MonoidHom.coe_coe,map_mul,map_inv]
  have hle : (((Tbar : Subgroup Q) ⊓ N).map (MulAut.conj (f g)).toMonoidHom) ≤
      (Tbar : Subgroup Q) := by
    rw [←hmap,←hconj]
    exact map_mono hg
  have he := normal_intersection_weakly_closed N Tbar (f g) hle
  rw [←hmap,←hconj] at he
  have hkerCg : f.ker ≤ (B.pCoreIn 2).map (MulAut.conj g).toMonoidHom := by
    have hn : f.ker.map (MulAut.conj g).toMonoidHom = f.ker :=
      mem_normalizer_iff_map_conj_eq.mp (show g ∈ normalizer (f.ker : Set G) by
        simp only [normalizer_eq_top,mem_top])
    exact hn ▸ map_mono hkerC
  have hh := congrArg (comap f) he
  rwa [comap_map_eq_self hkerCg,comap_map_eq_self hkerC] at hh

end Theory.AlternatingFive

namespace Theory.AlternatingFive
open Subgroup
variable {Q : Type*} [Group Q]
local notation "A5" => alternatingGroup (Fin 5)
local notation "W5" => RegularWreathProduct (Equiv.Perm (Fin 5)) (Multiplicative (ZMod 2))

/-- A literal symmetric-five wreath quotient contains its normal A₅ square. -/
theorem wreath_normal_square (e : Q ≃* W5) :
    ∃ N : Subgroup Q, N.Normal ∧ Nonempty (N ≃* A5 × A5) := by
  let a := e.trans Theory.SpecificGroups.Alternating.FiveSquareAutomorphisms.wreathEquiv
  let I := MulAut.innerSubgroup (A5 × A5)
  let N := I.comap a.toMonoidHom
  have hz : center (A5 × A5) = ⊥ := by
    rw [Subgroup.center_prod,alternatingGroup.center_eq_bot (by simp),bot_prod_bot]
  let ei : (A5 × A5) ≃* I := MonoidHom.ofInjective
    (MulAut.conj_injective_of_center_eq_bot hz)
  let en : N ≃* I := MulEquiv.ofBijective (a.toMonoidHom.subgroupComap I)
    ⟨fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h)),
      a.toMonoidHom.subgroupComap_surjective_of_surjective I a.surjective⟩
  exact ⟨N,inferInstance,⟨en.trans ei.symm⟩⟩

end Theory.AlternatingFive
