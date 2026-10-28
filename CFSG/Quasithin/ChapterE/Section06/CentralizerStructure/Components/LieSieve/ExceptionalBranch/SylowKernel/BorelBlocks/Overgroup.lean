module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.SylowKernel.Reduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalBranch.LocalSubgroups
public import Theory.GroupTheory.ComponentLocalOrbitEmbedding
public import Theory.GroupTheory.ComponentLocalDirectPower
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# The full Q-orbit of an exceptional component Borel

Let L be an A₅ component of C_G(U), Q = C_T(V), and S the Sylow subgroup
with ambient image L ∩ Q. The stabilizer N_Q(L) normalizes the embedded
Borel B = N_L(S). Thus the relative component-orbit theorem applies to
B ⊔ Q: its two-core is self-centralizing. No normalization of L by all
of Q is imposed.

The orbit of B is a direct power of its solvable A₄ seed, normal in B ⊔ Q
with two-group quotient. Hence the overgroup is solvable. In the non-Borel
branch L ∩ M = L ∩ Q, the order-twelve Borel cannot lie in M.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259); the relative component-orbit step is
2.3.9(7), printed p.526. These are the overgroup prerequisites, not a
claim that the Borel has already been placed in an E.6.7 block.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem embedded_normalizer (L : Subgroup G) (S : Sylow 2 L) :
    (normalizer (S : Set L)).map L.subtype =
      normalizer ((S : Subgroup L).map L.subtype : Set G) ⊓ L := by
  rw [← subgroupOf_map_subtype]
  congr 1
  rw [subgroupOf_normalizer_eq (map_subtype_le _)]
  congr 1
  exact congrArg (fun P : Subgroup L => (P : Set L))
    ((S : Subgroup L).comap_map_eq_self_of_injective L.subtype_injective).symm

omit [Finite G] in
/-- The component stabilizer in Q preserves the actual Borel. -/
theorem stabilizer_normalizes {L Q : Subgroup G} (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ Q) :
    Q ⊓ normalizer (L : Set G) ≤
      normalizer ((normalizer (S : Set L)).map L.subtype : Set G) := by
  have hn : Q ⊓ normalizer (L : Set G) ≤ normalizer (L ⊓ Q : Set G) :=
    (le_inf inf_le_right (inf_le_left.trans Q.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  rw [embedded_normalizer, hS]
  exact (le_inf (hn.trans (normalizer (L ⊓ Q : Set G)).le_normalizer) inf_le_right).trans
    inf_normalizer_le_normalizer_inf

omit [Finite G] in
private theorem center_eq_bot (e : G ≃* alternatingGroup (Fin 5)) : center G = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : e x ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
  rw [alternatingGroup.center_eq_bot (by simp)] at he
  exact mem_bot.mpr (e.injective ((mem_bot.mp he).trans (map_one e).symm))

private theorem centralizer_sylow_le (e : G ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 G) : centralizer (S : Set G) ≤ S := by
  intro x hx
  obtain ⟨s, hs, he⟩ := Theory.PSL2.SylowFixedQuotients.sylow_fixed_inner_of_equiv_five
    e S (MulAut.conj x) (by
      intro y hy
      change x * y * x⁻¹ = y
      rw [← mem_centralizer_iff.mp hx y hy]
      simp)
  have hc : s⁻¹ * x ∈ center G := by
    apply mem_center_iff.mpr
    intro y
    have hh : MulAut.conj (s⁻¹ * x) = 1 := by rw [map_mul, map_inv, he, inv_mul_cancel]
    have hxy := MulEquiv.congr_fun hh y
    change (s⁻¹ * x) * y * (s⁻¹ * x)⁻¹ = y at hxy
    exact (mul_inv_eq_iff_eq_mul.mp hxy).symm
  rw [center_eq_bot e, mem_bot] at hc
  have : x = s := (inv_mul_eq_one.mp hc).symm
  exact this ▸ hs

private theorem normalizer_characteristicTwo (e : G ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 G) : HasCharacteristicTwo (normalizer (S : Set G)) := by
  have hcore : (S : Subgroup G) ≤ (normalizer (S : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes S.isPGroup' le_normalizer le_rfl
  apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
  exact (inf_le_right.trans (Subgroup.centralizer_le hcore)).trans
    ((centralizer_sylow_le e S).trans hcore)


private theorem normalizer_card (e : G ≃* alternatingGroup (Fin 5)) (S : Sylow 2 G) :
    Nat.card (normalizer (S : Set G)) = 12 := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hn : (normalizer (S : Set G)).map e.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    change (normalizer ((S : Subgroup G) : Set G)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hi
  rw [← card_map_of_injective (K := normalizer (S : Set G)) (f := e.toMonoidHom)
    e.injective, hn, Nat.card_eq_fintype_card]
  have hc : ∀ i : Fin 5,
      Fintype.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
    decide +kernel
  exact hc i

private theorem normalizer_solvable (e : G ≃* alternatingGroup (Fin 5)) (S : Sylow 2 G) :
    Group.IsSolvable (normalizer (S : Set G)) := by
  apply alternatingGroup.isSolvable_subgroup_of_equiv_five e
  intro he
  have hc := normalizer_card e S
  rw [he, Nat.card_congr topEquiv.toEquiv, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup] at hc
  norm_num [Nat.factorial] at hc

variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- The Borel with the full Q-orbit adjoined has characteristic two. -/
theorem overgroup_characteristicTwo
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    HasCharacteristicTwo
      ((normalizer (S : Set L)).map L.subtype ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let B := (normalizer (S : Set L)).map L.subtype
  have hB : B ⊓ centralizer (B.pCoreIn 2 : Set G) ≤ B.pCoreIn 2 := by
    have hi := (inf_centralizer_pCoreIn_le_iff 2 (normalizer (S : Set L))).mpr
      (normalizer_characteristicTwo (e.trans eA) S)
    have hh := (inf_centralizer_map_le_iff _ _ L.subtype L.subtype_injective).mpr hi
    rwa [map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective] at hh
  apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
  exact hL.2.relative_local_adjoin_centralizer hL.1 (map_subtype_le _)
    (inf_le_right.trans (Subgroup.centralizer_le hU.1))
    (T.isPGroup'.to_le inf_le_left) (stabilizer_normalizes S hS) hB

private theorem relative_local_solvable {C B Q L : Subgroup G}
    (hL : ComponentIn C L) (e : L ≃* alternatingGroup (Fin 5)) (hBL : B ≤ L)
    (hQC : Q ≤ C) (hQ : IsPGroup 2 Q) (hB : Group.IsSolvable B)
    (hinv : Q ⊓ normalizer (L : Set G) ≤ normalizer (B : Set G)) :
    Group.IsSolvable (B ⊔ Q : Subgroup G) := by
  let B' := B.subgroupOf C
  let Q' := Q.subgroupOf C
  have hBC := hBL.trans hL.1
  have hmB : B'.map C.subtype = B := map_subgroupOf_eq_of_le hBC
  have hmQ : Q'.map C.subtype = Q := map_subgroupOf_eq_of_le hQC
  have hn : Q' ⊓ normalizer (L.subgroupOf C : Set C) ≤ normalizer (B' : Set C) := by
    rw [← subgroupOf_normalizer_eq hL.1, ← subgroupOf_normalizer_eq hBC]
    exact fun _ hx => hinv hx
  have hz : center (L.subgroupOf C) = ⊥ :=
    center_eq_bot ((subgroupOfEquivOfLe hL.1).trans e)
  obtain ⟨N, hN, hp, n, ⟨f⟩⟩ := hL.2.local_adjoin_normal_power hz
    (subgroupOf_mono C hBL) hn hQ.comap_subtype
  let := hN
  let := hB
  let : Group.IsSolvable B' := Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe hBC).symm.toMonoidHom)
    (subgroupOfEquivOfLe hBC).symm.surjective
  let : Group.IsSolvable (Fin n → B') := Group.isSolvable_finite_pi (fun _ : Fin n => B')
  let : Group.IsSolvable N := Group.isSolvable_of_surjective (f := f.symm.toMonoidHom) f.symm.surjective
  let : Group.IsSolvable ((B' ⊔ Q' : Subgroup C) ⧸ N) := by
    let := hp.isNilpotent
    infer_instance
  let : Group.IsSolvable (B' ⊔ Q' : Subgroup C) :=
    (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
  have hm : (B' ⊔ Q').map C.subtype = B ⊔ Q := by rw [Subgroup.map_sup, hmB, hmQ]
  exact Group.isSolvable_of_surjective (f := ((equivMapOfInjective (B' ⊔ Q') C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hm)).toMonoidHom)
    ((equivMapOfInjective (B' ⊔ Q') C.subtype C.subtype_injective).trans
      (MulEquiv.subgroupCongr hm)).surjective

/-- The full Borel-orbit overgroup is solvable, even when Q permutes components. -/
theorem overgroup_solvable
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    Group.IsSolvable
      ((normalizer (S : Set L)).map L.subtype ⊔ sylowCentralizer (T : Subgroup G) V : Subgroup G) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  let := normalizer_solvable (e.trans eA) S
  apply relative_local_solvable hL (e.trans eA) (map_subtype_le _)
    (inf_le_right.trans (Subgroup.centralizer_le hU.1))
    (T.isPGroup'.to_le inf_le_left) _ (stabilizer_normalizes S hS)
  exact Group.isSolvable_of_surjective (L.subtype.subgroupMap_surjective _)


/-- The non-Borel intersection excludes the entire embedded Borel from M. -/
theorem borel_not_le (hm : ClassicalGroup.IsPSL L 2 4)
    (hLM : L ⊓ M = L ⊓ sylowCentralizer (T : Subgroup G) V)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    ¬ (normalizer (S : Set L)).map L.subtype ≤ M := by
  intro hBM
  have hBS : normalizer (S : Set L) ≤ (S : Subgroup L) := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hS, ← hLM]
    exact le_inf (map_subtype_le _) hBM
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  have hd := card_dvd_of_le hBS
  rw [normalizer_card (e.trans eA) S,
    Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five (e.trans eA) S] at hd
  norm_num at hd

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch.SylowKernel.BorelBlocks
