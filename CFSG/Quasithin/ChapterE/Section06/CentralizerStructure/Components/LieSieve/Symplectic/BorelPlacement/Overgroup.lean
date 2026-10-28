module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.Symplectic.BorelPlacement.Seed
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.ComponentLocalDirectPower
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.BlockSelection.Contracts

/-!
# The actual symplectic Borel-orbit overgroup

For the Borel B marked by S = L ∩ Q, the stabilizer N_Q(L) normalizes B.
Apply the component-orbit theorem inside H, where L is subnormal, to show
that B joined with Q has characteristic two. Its normal orbit layer is a
finite direct power of B and its quotient is a two-group, so it is solvable.
This constructs the premises needed to apply the complete E.6.7 input.

Two-perfection places any candidate block in that orbit layer. Its subnormal
embedding in a direct power of the actual matrix Borel is exported without
changing its domain group. No assumption that Q normalizes L is needed.
The remaining intrinsic exclusion of alternating-three blocks is separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259), and 2.3.9(7), printed pp.525–526.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G] {L Q H : Subgroup G}

omit [Finite G] in
private theorem embedded_normalizer (S : Sylow 2 L) :
    markedBorel S = normalizer ((S : Subgroup L).map L.subtype : Set G) ⊓ L := by
  rw [markedBorel, ← subgroupOf_map_subtype]
  congr 1
  rw [subgroupOf_normalizer_eq (map_subtype_le _)]
  congr 1
  exact congrArg (fun P : Subgroup L => (P : Set L))
    ((S : Subgroup L).comap_map_eq_self_of_injective L.subtype_injective).symm

omit [Finite G] in
/-- Only the stabilizer of the component is needed, even if Q permutes components. -/
theorem stabilizer_normalizes_borel (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    Q ⊓ normalizer (L : Set G) ≤ normalizer (markedBorel S : Set G) := by
  have hn : Q ⊓ normalizer (L : Set G) ≤ normalizer (L ⊓ Q : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans Q.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [embedded_normalizer, hS]
  exact (le_inf (hn.trans (normalizer (L ⊓ Q : Set G)).le_normalizer) inf_le_right).trans
    inf_normalizer_le_normalizer_inf

/-- Characteristic two for the actual join of the Borel and the marked two-group. -/
theorem overgroup_characteristicTwo (hL : ComponentIn H L)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) {n : ℕ} (hm : SymplecticDerivedModel L n)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    HasCharacteristicTwo (markedBorel S ⊔ Q : Subgroup G) := by
  have hB : markedBorel S ⊓ centralizer ((markedBorel S).pCoreIn 2 : Set G) ≤
      (markedBorel S).pCoreIn 2 := by
    have hi := (inf_centralizer_pCoreIn_le_iff 2 (normalizer (S : Set L))).mpr
      (normalizer_characteristicTwo hm S)
    have hh := (inf_centralizer_map_le_iff _ _ L.subtype L.subtype_injective).mpr hi
    rwa [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective] at hh
  apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
  exact hL.2.relative_local_adjoin_centralizer hL.1 (markedBorel_le S) hQH hQ
    (stabilizer_normalizes_borel S hS) hB

/-- Work inside H, where the component really is subnormal. -/
theorem overgroup_solvable (hL : ComponentIn H L)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) {n : ℕ} (hm : SymplecticDerivedModel L n)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    Group.IsSolvable (markedBorel S ⊔ Q : Subgroup G) := by
  let B := markedBorel S
  let B' := B.subgroupOf H
  let Q' := Q.subgroupOf H
  have hBH : B ≤ H := (markedBorel_le S).trans hL.1
  have hmB : B'.map H.subtype = B := map_subgroupOf_eq_of_le hBH
  have hmQ : Q'.map H.subtype = Q := map_subgroupOf_eq_of_le hQH
  have hn : Q' ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (B' : Set H) := by
    rw [← subgroupOf_normalizer_eq hL.1, ← subgroupOf_normalizer_eq hBH]
    exact fun _ hx => stabilizer_normalizes_borel S hS hx
  have hz : center (L.subgroupOf H) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : (subgroupOfEquivOfLe hL.1) x ∈ center L :=
      (centerCongr (subgroupOfEquivOfLe hL.1) ⟨x, hx⟩).property
    rw [model_center_eq_bot hm, mem_bot] at he
    exact mem_bot.mpr ((subgroupOfEquivOfLe hL.1).injective
      (he.trans (map_one _).symm))
  obtain ⟨N, hN, hp, k, ⟨f⟩⟩ := hL.2.local_adjoin_normal_power hz
    (subgroupOf_mono H (markedBorel_le S)) hn hQ.comap_subtype
  let _ := hN
  let _ := markedBorel_solvable hm S
  let _ : Group.IsSolvable B' := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe hBH).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBH).symm.surjective
  let _ : Group.IsSolvable (Fin k → B') := Group.isSolvable_finite_pi (fun _ : Fin k => B')
  let _ : Group.IsSolvable N := Group.isSolvable_of_surjective (f := f.symm.toMonoidHom)
    f.symm.surjective
  let _ : Group.IsSolvable ((B' ⊔ Q' : Subgroup H) ⧸ N) := by
    let _ := hp.isNilpotent
    infer_instance
  let _ : Group.IsSolvable (B' ⊔ Q' : Subgroup H) :=
    (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
  have he : (B' ⊔ Q').map H.subtype = B ⊔ Q := by rw [Subgroup.map_sup, hmB, hmQ]
  exact Group.isSolvable_of_surjective (f := ((equivMapOfInjective (B' ⊔ Q') H.subtype
    H.subtype_injective).trans (MulEquiv.subgroupCongr he)).toMonoidHom)
    ((equivMapOfInjective (B' ⊔ Q') H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr he)).surjective

/-- A two-perfect subnormal subgroup of the actual local join embeds subnormally
in a finite power of its Borel seed. The domain group is preserved. -/
theorem overgroup_embedding (hL : ComponentIn H L)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) {n : ℕ} (hm : SymplecticDerivedModel L n)
    (S : Sylow 2 L) (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    {X : Type*} [Group X] (hp : IsPPerfect 2 X)
    (f : X →* (markedBorel S ⊔ Q : Subgroup G)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) :
    ∃ (k : ℕ) (g : X →* (Fin k → markedBorel S)),
      Function.Injective g ∧ g.range.IsSubnormal := by
  let B := markedBorel S
  let B' := B.subgroupOf H
  let Q' := Q.subgroupOf H
  have hBH : B ≤ H := (markedBorel_le S).trans hL.1
  have hmB : B'.map H.subtype = B := map_subgroupOf_eq_of_le hBH
  have hmQ : Q'.map H.subtype = Q := map_subgroupOf_eq_of_le hQH
  have hn : Q' ⊓ normalizer (L.subgroupOf H : Set H) ≤ normalizer (B' : Set H) := by
    rw [← subgroupOf_normalizer_eq hL.1, ← subgroupOf_normalizer_eq hBH]
    exact fun _ hx => stabilizer_normalizes_borel S hS hx
  have hz : center (L.subgroupOf H) = ⊥ := by
    apply bot_unique
    intro x hx
    have he : (subgroupOfEquivOfLe hL.1) x ∈ center L :=
      (centerCongr (subgroupOfEquivOfLe hL.1) ⟨x, hx⟩).property
    rw [model_center_eq_bot hm, mem_bot] at he
    exact mem_bot.mpr ((subgroupOfEquivOfLe hL.1).injective
      (he.trans (map_one _).symm))
  have he : (B' ⊔ Q').map H.subtype = B ⊔ Q := by rw [Subgroup.map_sup, hmB, hmQ]
  let e : (B' ⊔ Q' : Subgroup H) ≃* (B ⊔ Q : Subgroup G) :=
    (equivMapOfInjective (B' ⊔ Q') H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr he)
  let f' := e.symm.toMonoidHom.comp f
  have hs' : f'.range.IsSubnormal := by
    rw [MonoidHom.range_comp]
    exact hs.map e.symm.surjective
  obtain ⟨k, g, hg, hsg⟩ := hL.2.local_adjoin_embedding hz
    (subgroupOf_mono H (markedBorel_le S)) hn hQ.comap_subtype hp f'
    (e.symm.injective.comp hf) hs'
  let ep : (Fin k → B') ≃* (Fin k → B) :=
    MulEquiv.piCongrRight (fun _ => subgroupOfEquivOfLe hBH)
  refine ⟨k, ep.toMonoidHom.comp g, ep.injective.comp hg, ?_⟩
  rw [MonoidHom.range_comp]
  exact hsg.map ep.surjective

/-- For n greater than one the coordinate target is the literal matrix Borel,
with its field size and each subgroup embedding retained. -/
theorem overgroup_matrix_embedding (hL : ComponentIn H L)
    (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) {n : ℕ} (hm : SymplecticDerivedModel L n)
    (hn : 1 < n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q)
    {X : Type*} [Group X] (hp : IsPPerfect 2 X)
    (f : X →* (markedBorel S ⊔ Q : Subgroup G)) (hf : Function.Injective f)
    (hs : f.range.IsSubnormal) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2), Nat.card F = 2 ^ n ∧
      ∃ (k : ℕ) (g : X →* (Fin k → Theory.SpecificGroups.SymplecticFour.borel (F := F))),
        Function.Injective g ∧ g.range.IsSubnormal := by
  obtain ⟨F, hfield, hfinite, hchar, hF, ⟨e⟩⟩ := exists_standardBorel_equiv hm hn S
  obtain ⟨k, g, hg, hsg⟩ := overgroup_embedding hL hQH hQ hm S hS hp f hf hs
  let ep := MulEquiv.piCongrRight (fun _ : Fin k => e)
  refine ⟨F, hfield, hfinite, hchar, hF, k, ep.toMonoidHom.comp g, ep.injective.comp hg, ?_⟩
  rw [MonoidHom.range_comp]
  exact hsg.map ep.surjective

variable {T : Sylow 2 G} {M V U : Subgroup G}

/-- E.6.7 is applied to B joined with all of Q, with its characteristic-two premise proved. -/
theorem overgroup_decomposition (input : E67Input T M V)
    (hU : U ∈ obstructionFamily M V) (hL : ComponentIn (centralizer (U : Set G)) L)
    {n : ℕ} (hm : SymplecticDerivedModel L n) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    Nonempty (E67Decomposition (sylowCentralizer (T : Subgroup G) V) M V U
      (markedBorel S ⊔ sylowCentralizer (T : Subgroup G) V)) := by
  have hQH : sylowCentralizer (T : Subgroup G) V ≤ centralizer (U : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le hU.1)
  exact input U hU _ le_sup_right (sup_le ((markedBorel_le S).trans hL.1) hQH)
    (overgroup_characteristicTwo hL hQH (T.isPGroup'.to_le inf_le_left) hm S hS)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.Symplectic.BorelPlacement
