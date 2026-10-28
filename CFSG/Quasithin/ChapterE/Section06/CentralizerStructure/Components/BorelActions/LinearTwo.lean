module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.BorelActions.Reduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import Theory.SpecificGroups.SL2.EvenBorel
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The PSL₂ Borel witness in E.6.11

Sylow conjugacy aligns the upper unipotents in the actual SL₂ model with
the prescribed Sylow subgroup of L. Both that subgroup and the displacement
[V,L ∩ M] have order 2ⁿ, and the common reduction puts the displacement in
its center. They are therefore equal. The unipotent centralizer calculation
then identifies C_L(V) with this Sylow subgroup.

In characteristic two the center of L is trivial. The Borel-preimage clause
of E.6.8 consequently identifies L ∩ M with the normalizer of the prescribed
Sylow subgroup. The diagonal torus, transported through the same equivalence,
is the required cyclic complement. This argument requires neither maximality
of U nor normality of L in its ambient centralizer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1)
and the Borel case of E.6.11, printed pp.247,249–250.
-/

public section

open Subgroup BenderSuzuki.Converse Matrix
open Theory.SpecificGroups.SL2.EvenBorel

namespace CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
open CFSG.Quasithin.ChapterF.Source.Linear

variable {G : Type*} [Group G] [Finite G]
variable {M V U Q L : Subgroup G} {n : ℕ}

private theorem borelPreimage_eq_normalizer_of_center_eq_bot (hcenter : center L = ⊥) (hb : BorelPreimage L (L ⊓ M))
    (S : Sylow 2 L) (hSM : (S : Subgroup L) ≤ (L ⊓ M).subgroupOf L) :
    (L ⊓ M).subgroupOf L = normalizer (S : Set L) := by
  obtain ⟨_, R, hR⟩ := hb
  let q := QuotientGroup.mk' (center L)
  have hq : Function.Bijective q :=
    ⟨((MonoidHom.ker_eq_bot_iff q).mp (by rw [QuotientGroup.ker_mk', hcenter])),
      QuotientGroup.mk'_surjective _⟩
  let S' := S.mapSurjective hq.2
  have hle : (S' : Subgroup (L ⧸ center L)) ≤ normalizer (R : Set (L ⧸ center L)) := by
    change (S : Subgroup L).map q ≤ _
    apply map_le_iff_le_comap.mpr
    exact hSM.trans hR.le
  have hSR : (S' : Subgroup (L ⧸ center L)) ≤ R := by
    have he := S'.isPGroup'.inf_normalizer_sylow R
    rw [inf_eq_left.mpr hle] at he
    exact inf_eq_left.mp he.symm
  have hRS : (R : Subgroup (L ⧸ center L)) = (S' : Subgroup (L ⧸ center L)) :=
    S'.is_maximal' R.isPGroup' hSR
  apply Subgroup.map_injective hq.1
  rw [hR, map_comap_eq_self_of_surjective hq.2]
  change normalizer (R : Set (L ⧸ center L)) =
    (normalizer ((S : Subgroup L) : Set L)).map q
  rw [map_normalizer_eq_of_bijective (S : Subgroup L) hq]
  exact congrArg (fun A : Subgroup (L ⧸ center L) => normalizer (A : Set (L ⧸ center L))) hRS

private theorem exists_unipotent_aligned_equiv {H : Type*} [Group H] [Finite H] {F : Type*} [Field F] [Finite F]
    [CharP F 2] (e₀ : SL2 F ≃* H) (S : Sylow 2 H) :
    ∃ e : SL2 F ≃* H, (Unip F).map e.toMonoidHom = S := by
  let R := (SpecialLinearGroup.upperUnipotentSylow F 2).mapSurjective (f := e₀.toMonoidHom) e₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H R S
  refine ⟨e₀.trans (MulAut.conj g), ?_⟩
  change (Unip F).map ((MulAut.conj g).toMonoidHom.comp e₀.toMonoidHom) = _
  rw [← Subgroup.map_map, unip_eq_upper]
  change (R : Subgroup H).map (MulAut.conj g).toMonoidHom = _
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

private theorem torus_cyclic {F : Type*} [Field F] [Finite F]
    (hcard : Nat.card F = 2 ^ n) :
    Nonempty (Torus F ≃* Multiplicative (ZMod (2 ^ n - 1))) := by
  let e : Fˣ ≃* Torus F :=
    (MonoidHom.ofInjective (torHom_injective (F := F))).trans
      (MulEquiv.subgroupCongr Torus_eq_range.symm)
  refine ⟨e.symm.trans (mulEquivOfCyclicCardEq ?_)⟩
  rw [Nat.card_units, hcard]
  exact (Nat.card_zmod _).symm

/-- The PSL₂ model supplies the actual embedded cyclic Borel complement and
the Sylow-center containment required in E.6.11(3b). -/
theorem modelWitness_linear_two
    {K : GroupClass} {T : Sylow 2 G}
    (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (b : BorelAlternative M V U L n) (hn : 1 < n)
    (hVL : V ≤ normalizer (L : Set G))
    (hQ : Q = sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    (hmodel : ClassicalGroup.IsPSL L 2 (2 ^ n)) : ModelWitness M V Q L n := by
  obtain ⟨F, hF, hfin, hcard, ⟨f⟩⟩ := hmodel
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  let e₀ : SL2 F ≃* L :=
    (MulEquiv.ofBijective (pi F) ⟨pi_injective, pi_surjective⟩).trans f.symm
  obtain ⟨e, he⟩ := exists_unipotent_aligned_equiv e₀ S
  have hcS : Nat.card ↥(L ⊓ Q) = 2 ^ n := by
    rw [← hS, card_map_of_injective L.subtype_injective, ← he,
      card_map_of_injective e.injective, unip_eq_upper,
      SpecialLinearGroup.card_upperUnipotent, hcard]
  have hWS : ⁅V, L ⊓ M⁆ = L ⊓ Q :=
    eq_of_le_of_card_ge
      ((displacement_le_center h hU hL hVL hQ).trans (map_subtype_le _))
      (by rw [hcS, displacement_card h b hn])
  have hCU : centralizer (Unip F : Set (SL2 F)) = Unip F := by
    simpa only [unip_eq_upper] using (unipotent_centralizer (F := F))
  have hCV : L ⊓ centralizer (V : Set G) = L ⊓ Q := by
    apply le_antisymm
    · intro x hx
      have hxW : x ∈ centralizer ((L ⊓ Q : Subgroup G) : Set G) := by
        rw [← hWS]
        exact ((displacement_centralizer b hn).symm ▸ hx).2
      have hxU : e.symm ⟨x, hx.1⟩ ∈ centralizer (Unip F : Set (SL2 F)) := by
        apply mem_centralizer_iff.mpr
        intro u hu
        apply e.injective
        apply Subtype.ext
        have huS : (e u : G) ∈ L ⊓ Q :=
          hS ▸ mem_map_of_mem L.subtype (he ▸ mem_map_of_mem e.toMonoidHom hu)
        simpa only [map_mul, e.apply_symm_apply, Subgroup.coe_mul] using
          mem_centralizer_iff.mp hxW (e u) huS
      have hxS : (⟨x, hx.1⟩ : L) ∈ (S : Subgroup L) := by
        rw [← he]
        exact ⟨e.symm ⟨x, hx.1⟩, hCU ▸ hxU, e.apply_symm_apply _⟩
      exact hS ▸ mem_map_of_mem L.subtype hxS
    · intro x hx
      refine ⟨hx.1, ?_⟩
      rw [hQ] at hx
      exact hx.2.2
  have hcenter : center L = ⊥ := by
    apply (center L).eq_bot_iff_forall.mpr
    intro x hx
    have hxc : e.symm x ∈ center (SL2 F) := by
      apply mem_center_iff.mpr
      intro y
      apply e.injective
      simpa only [map_mul, e.apply_symm_apply] using mem_center_iff.mp hx (e y)
    have hx1 : e.symm x = 1 := by
      simpa only [center_SL2_eq_bot, mem_bot] using hxc
    exact e.symm.injective (hx1.trans (map_one e.symm).symm)
  have hSM : (S : Subgroup L) ≤ (L ⊓ M).subgroupOf L := by
    intro x hx
    have hxQ : (x : G) ∈ L ⊓ Q := hS ▸ mem_map_of_mem L.subtype hx
    rw [hQ] at hxQ
    exact ⟨x.property, h.sylow_le hxQ.2.1⟩
  have hB : (normalizer (S : Set L)).map L.subtype = L ⊓ M := by
    rw [← borelPreimage_eq_normalizer_of_center_eq_bot hcenter b.borel S hSM, map_subgroupOf_eq_of_le inf_le_left]
  have hnmap : (Borel F).map e.toMonoidHom = normalizer (S : Set L) := by
    rw [← unip_normalizer, map_equiv_normalizer_eq, he]
    rfl
  let X : Subgroup G := ((Torus F).map e.toMonoidHom).map L.subtype
  have hX : X ≤ L ⊓ M := by
    rw [← hB, ← hnmap]
    exact map_mono (map_mono Torus_le_Borel)
  refine ⟨⟨X, hX, ?_, ?_, ?_⟩, ?_⟩
  · obtain ⟨et⟩ := torus_cyclic hcard
    exact ⟨(((e.subgroupMap (Torus F)).trans
      (((Torus F).map e.toMonoidHom).equivMapOfInjective L.subtype
        L.subtype_injective)).symm).trans et⟩
  · rw [hCV, ← hS]
    change (S : Subgroup L).map L.subtype ⊔
      ((Torus F).map e.toMonoidHom).map L.subtype = _
    rw [← Subgroup.map_sup, ← he, ← Subgroup.map_sup, Unip_sup_Torus, hnmap, hB]
  · rw [hCV, ← hS]
    change (S : Subgroup L).map L.subtype ⊓
      ((Torus F).map e.toMonoidHom).map L.subtype = _
    rw [← map_inf _ _ _ L.subtype_injective, ← he,
      ← map_inf _ _ _ e.injective, disjoint_iff.mp Unip_disjoint_Torus,
      Subgroup.map_bot, Subgroup.map_bot]
  · exact (map_subtype_le _).trans (hWS.symm ▸ le_sup_right)

end CFSG.Quasithin.ChapterE.Section06.Components.BorelActions
