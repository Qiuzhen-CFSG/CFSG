module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.LocalSubgroups
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts

/-!
# Detecting the exceptional component action on its Borel

An automorphism of A₅ fixing a Sylow four-group pointwise is conjugation
by an element of that four-group. The Borel is a point stabilizer A₄
with trivial centralizer in A₅, so restriction to the Borel detects the
whole component action kernel.

Consequently a Borel contained in an alternating block from the genuine
E.6.7 decomposition gives an upper bound of one on the component action
corank. Positivity then makes the bound an equality. The concrete block
overgroup is an explicit witness, whose construction remains separate.
No normalization of the component by Q, maximality of U, or equality
between U and the action kernel is asserted by this reduction.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem centralizer_stabilizer_eq_bot (i : Fin 5) :
    centralizer (MulAction.stabilizer (alternatingGroup (Fin 5)) i :
      Set (alternatingGroup (Fin 5))) = ⊥ := by
  have hc : ∀ i : Fin 5, ∀ x : alternatingGroup (Fin 5),
      (∀ y : alternatingGroup (Fin 5), y.val i = i → y * x = x * y) → x = 1 := by
    decide +kernel
  apply eq_bot_iff.mpr
  intro x hx
  exact mem_bot.mpr (hc i x (fun y hy => (mem_centralizer_iff.mp hx y hy)))

private theorem centralizer_sylow_normalizer_eq_bot
    (e : L ≃* alternatingGroup (Fin 5)) (S : Sylow 2 L) :
    centralizer (normalizer (S : Set L) : Set L) = ⊥ := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hn : (normalizer (S : Set L)).map e.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    change (normalizer ((S : Subgroup L) : Set L)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hi
  apply eq_bot_iff.mpr
  intro x hx
  have he : e x ∈ centralizer (MulAction.stabilizer (alternatingGroup (Fin 5)) i :
      Set (alternatingGroup (Fin 5))) := by
    intro y hy
    obtain ⟨b, hb, rfl⟩ := hn.symm ▸ hy
    change e b * e x = e x * e b
    simpa only [map_mul] using congrArg e (mem_centralizer_iff.mp hx b hb)
  rw [centralizer_stabilizer_eq_bot] at he
  exact mem_bot.mpr (e.injective ((mem_bot.mp he).trans (map_one e).symm))

/-- The actual Borel detects the same kernel as the whole PSL₂(4) component
for every group of automorphisms fixing its Sylow subgroup pointwise. -/
theorem fixedSpace_eq_borel
    (hm : ClassicalGroup.IsPSL L 2 4) (hN : V ≤ normalizer (L : Set G))
    (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G)) :
    V ⊓ centralizer ((normalizer (S : Set L)).map L.subtype : Set G) =
      V ⊓ centralizer (L : Set G) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let f := e.trans eA
  apply le_antisymm
  · rintro v ⟨hv, hc⟩
    let a := L.normalizerMonoidHom ⟨v, hN hv⟩
    obtain ⟨s, _, hs⟩ := Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five
      f S a (fun x hx => Subtype.ext (hfix v hv ⟨x, hx⟩))
    have hsc : s ∈ centralizer (normalizer (S : Set L) : Set L) := by
      intro b hb
      have hav : a b = b := by
        apply Subtype.ext
        change v * (b : G) * v⁻¹ = b
        rw [← mem_centralizer_iff.mp hc b (mem_map_of_mem L.subtype hb)]
        simp
      rw [hs] at hav
      have hh : s * b * s⁻¹ = b := hav
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    rw [centralizer_sylow_normalizer_eq_bot f S] at hsc
    have ha : a = 1 := by rw [hs, mem_bot.mp hsc, map_one]
    refine ⟨hv, ?_⟩
    intro l hl
    have hh := congrArg (fun b : L => (b : G)) (MulEquiv.congr_fun ha ⟨l, hl⟩)
    change v * l * v⁻¹ = l at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · exact inf_le_inf_left V (Subgroup.centralizer_le (map_subtype_le _))

/-- In the source setup the kernel detection uses the embedded Sylow
intersection, without requiring Q to normalize the component. -/
theorem component_fixedSpace_eq_borel
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) :
    ∃ S : Sylow 2 L,
      (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V ∧
      V ⊓ centralizer ((normalizer (S : Set L)).map L.subtype : Set G) =
        V ⊓ centralizer (L : Set G) := by
  obtain ⟨hN, S, hS, hfix⟩ := component_sylow_action h hU hL rfl
  exact ⟨S, hS, fixedSpace_eq_borel hm hN S hfix⟩

open InvariantSubspaces.BlockSelection

/-- A concrete overgroup and a block of its complete E.6.7 decomposition.
The intrinsic Borel is contained in that block. Constructing this witness
must handle all Q-conjugates of the component; it is not part of E.6.7. -/
structure BorelBlockWitness (T : Sylow 2 G) (M V U L : Subgroup G)
    (S : Sylow 2 L) where
  overgroup : Subgroup G
  contains_Q : sylowCentralizer (T : Subgroup G) V ≤ overgroup
  centralizes_U : overgroup ≤ centralizer (U : Set G)
  characteristicTwo : HasCharacteristicTwo overgroup
  decomposition : E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U overgroup
  index : Fin decomposition.count
  alternating : ChapterC.IsAlternatingBlock (decomposition.block index) 3
  borel_le : (normalizer (S : Set L)).map L.subtype ≤ decomposition.block index

/-- A Borel block bounds the component action by E.6.7(2), using the
proved equality of the two actual action kernels. This is conditional
on the displayed block witness and is not the completed Sylow branch. -/
theorem corank_one_of_borelBlockWitness
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (w : BorelBlockWitness T M V U L S) : actionCorank V L = 1 := by
  have hf := fixedSpace_eq_borel hm (component_normalized_by_V h hU hL) S (by
    intro v hv x
    have hx : ((x : L) : G) ∈ L ⊓ sylowCentralizer (T : Subgroup G) V :=
      hS ▸ mem_map_of_mem L.subtype x.property
    rw [mem_centralizer_iff.mp hx.2.2 v hv]
    simp)
  have hk : V ⊓ centralizer (w.decomposition.block w.index : Set G) ≤
      V ⊓ centralizer (L : Set G) := by
    rw [← hf]
    exact inf_le_inf_left V (Subgroup.centralizer_le w.borel_le)
  have hb := subgroupCorank_antitone (V := V) hk
  have hd := (w.decomposition.alternating w.index 3 w.alternating).1
  rw [hd] at hb
  have hp := fixedSpace_corank_pos h (component_not_le h earlier hU hL)
  change subgroupCorank V (V ⊓ centralizer (L : Set G)) = 1
  omega

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel
