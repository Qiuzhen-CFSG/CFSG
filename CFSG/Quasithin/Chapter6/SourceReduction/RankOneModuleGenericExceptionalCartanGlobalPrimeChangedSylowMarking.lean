module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeCommonOvergroup
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldCartan
public import Theory.GroupTheory.Hall.SylowConjugacy
public import Theory.GroupTheory.CyclicSubgroupNormalizer

/-!
# Marked Sylow conjugacy and the common-component subcase of 5.2.2

The changed Sylow has the original intersections with L, O²(H), and R.
Inside N_G(T₀), Hall conjugacy in N_L(T∩L) selects a Sylow conjugator
fixing the actual left Cartan and its prime actor D. Such a conjugator
must send R outside G₀T₀B: otherwise the latter's nontrivial two-core
would lie in the conjugate of DH, whose two-core is trivial.

If R is itself a C-component of X=⟨N_G(T₀),H⟩, source 1.2.1(3) makes
both Sylow orbit spans normal in X and hence equal. The marked conjugator
then preserves their common value O²(H), contradicting the escape above.
Thus a larger changed Sylow forces a strictly larger common component.
In particular maximality of R in L(G,T) closes the larger-Sylow branch.

The source moved-component maximality theorem, the construction of the
appropriate right-factor branch, the remaining larger-component cases,
and the smaller-Sylow exclusion remain with the 5.2.2 assembly. These
results do not assert the final Cartan normalization.

Source: Aschbacher--Smith 1.2.1(3), 1.2.4 and 1.2.8, pp.504--507,
and the changed-Sylow argument of 5.2.2, pp.648--649.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem intersection_eq_of_sylow_le
    {J Q Y : Subgroup G} (hQ : Chapter1.IsSylowIn 2 Q J)
    (hY : IsPGroup 2 Y) (hQY : Q ≤ Y) : Y ⊓ J = Q := by
  obtain ⟨_,hQJ,hm⟩ := Chapter1.isSylowIn_iff.mp hQ
  exact hm _ (hY.to_le inf_le_left) (le_inf hQY hQJ) inf_le_right

/-- The original Sylow intersections with L, O²(H), and R survive the change.
Each is already Sylow in its respective subgroup and is contained in T₀. -/
theorem LocalData.changedSylow_intersections
    {T : Sylow 2 G} {L W H B D R : Subgroup G} {n : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
    T₁ ⊓ L = (T : Subgroup G) ⊓ L ∧
      T₁ ⊓ residual H = (T : Subgroup G) ⊓ residual H ∧
      T₁ ⊓ R = (T : Subgroup G) ⊓ R := by
  let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
  have hp : IsPGroup 2 T₁ := P.isPGroup'.map _
  have hST := (d.sourceS_le_normalizingSylow h hH).trans hTP
  obtain ⟨Q,hQ⟩ := exists_sylow_component h.sylow_normalizes
  have hL : T₁ ⊓ L = (T : Subgroup G) ⊓ L := by
    apply intersection_eq_of_sylow_le ⟨Q,by simpa only [inf_comm] using hQ⟩ hp
    rw [←d.S_intersection_left]
    exact inf_le_left.trans hST
  obtain ⟨QK,hQK⟩ := NormalSylowQuotientAction.intersection_sylow T (residual H)
    (hH.1.1.2.trans (le_normalizer_residual H))
  have hK : T₁ ⊓ residual H = (T : Subgroup G) ⊓ residual H := by
    apply intersection_eq_of_sylow_le
      ⟨QK,by rw [hQK,subgroupOf_map_subtype]⟩ hp
    rw [←d.S_intersection_residual]
    exact inf_le_left.trans hST
  refine ⟨hL,hK,?_⟩
  calc
    T₁ ⊓ R = (T₁ ⊓ residual H) ⊓ R := by
      rw [inf_assoc,inf_eq_right.mpr d.right_le_residual]
    _ = ((T : Subgroup G) ⊓ residual H) ⊓ R := by rw [hK]
    _ = (T : Subgroup G) ⊓ R := by
      rw [inf_assoc,inf_eq_right.mpr d.right_le_residual]

/-- The full normalizer of T₀ preserves the original left Borel, using
T₀∩L=T∩L and the source rank-one normalizer bound. -/
theorem LocalData.normalizingSylow_normalizer_preserves_borel
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) :
    normalizer (normalizingSylow T R : Set G) ≤
      normalizer (localBorel T L : Set G) := by
  let N := normalizer (normalizingSylow T R : Set G)
  have hNL : N ≤ normalizer (L : Set G) :=
    d.normalizingSylow_normalizer_le h hH c hd hz
  have hUL : normalizingSylow T R ⊓ L = (T : Subgroup G) ⊓ L := by
    apply le_antisymm (inf_le_inf_right L inf_le_left)
    apply le_inf _ inf_le_right
    rw [←d.S_intersection_left]
    exact inf_le_left.trans (d.sourceS_le_normalizingSylow h hH)
  have hNU : N ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
    rw [←hUL]
    exact (le_inf le_rfl hNL).trans inf_normalizer_le_normalizer_inf
  exact (le_inf hNL (hNU.trans
    (normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- An ambient changed Sylow is conjugate to T by an element preserving
T₀, L, the actual left Hall Cartan, and its selected prime subgroup. -/
theorem LocalData.changedSylow_marked_conjugator
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hTU : normalizingSylow T R ≤ (U : Subgroup G)) :
    ∃ x : G, x ∈ normalizer (normalizingSylow T R : Set G) ∧
      x ∈ normalizer (L : Set G) ∧ x ∈ normalizer (A : Set G) ∧
      x ∈ normalizer (D : Set G) ∧
      (T : Subgroup G).map (MulAut.conj x).toMonoidHom = (U : Subgroup G) := by
  let N := normalizer (normalizingSylow T R : Set G)
  have hTN : (T : Subgroup G) ≤ N :=
    d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz T.isPGroup' inf_le_left
  have hUN : (U : Subgroup G) ≤ N :=
    d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup' hTU
  have hUL : (T : Subgroup G) ⊓ L ≤ (U : Subgroup G) := by
    rw [←d.S_intersection_left]
    exact inf_le_left.trans ((d.sourceS_le_normalizingSylow h hH).trans hTU)
  obtain ⟨P,hP⟩ := exists_sylow_localBorel T L h.sylow_normalizes
  obtain ⟨x,hxN,hxA,hx⟩ := OddHall.sylow_conjugate_fixing_hall
    N (localBorel T L) ((T : Subgroup G) ⊓ L) A T U hTN hUN hUL
    (d.normalizingSylow_normalizer_preserves_borel h hH c hd hz)
    (localBorel_isSolvable h.exponent h.linear h.sylow_normalizes)
    P hP c.left_le c.left_hall
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  exact ⟨x,hxN,d.normalizingSylow_normalizer_le h hH c hd hz hxN,hxA,
    normalizer_le_normalizer_of_le_cyclic D A hd.le_cartan hxA,hx⟩

omit [Finite G] in
/-- A conjugator preserving the prime actor must send R outside G₀T₀B.
Otherwise its nontrivial core lies in the conjugate of the zero-core join DH. -/
theorem LocalData.changedSylow_conjugate_outside
    {T U : Sylow 2 G} {L H A B D R : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D R) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    {x : G} (hxD : x ∈ normalizer (D : Set G))
    (hxT : (T : Subgroup G).map (MulAut.conj x).toMonoidHom = (U : Subgroup G)) :
    ¬ R.map (MulAut.conj x).toMonoidHom ≤ extension T L H B D R := by
  intro hR
  let f := (MulAut.conj x).toMonoidHom
  let E := extension T L H B D R
  let J := (D ⊔ H).map f
  have hD : D.map f = D := mem_normalizer_iff_map_conj_eq.mp hxD
  have hHE : H.map f ≤ E := by
    rw [←d.right_generate,Subgroup.map_sup,hxT]
    exact sup_le hR (hU ▸ map_subtype_le _)
  have hJE : J ≤ E := by
    dsimp only [J]
    rw [Subgroup.map_sup,hD]
    exact sup_le (le_sup_left.trans (le_sup_left.trans le_sup_left)) hHE
  have hUJ : (U : Subgroup G) ≤ J := by
    rw [←hxT]
    exact map_mono ((show (T : Subgroup G) ≤ H from d.right_generate ▸ le_sup_right).trans le_sup_right)
  have hcore : E.pCoreIn 2 ≤ J :=
    ((pCoreIn_le_sylow E P).trans_eq hU.symm).trans hUJ
  have hzJ : J.pCoreIn 2 = ⊥ := by
    change ((D ⊔ H).map f).pCoreIn 2 = ⊥
    rw [←map_pCoreIn_of_injective 2 (D ⊔ H) f (MulAut.conj x).injective,
      hd.zero_core,Subgroup.map_bot]
  exact d.extension_core_ne_bot hz (bot_unique
    (((le_inf hcore le_rfl).trans (inf_pCoreIn_le_of_le 2 hJE)).trans hzJ.le))

private theorem component_sylow_orbit_normalizes
    {X R : Subgroup G} (hRX : R ≤ X)
    (hQ : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X))
    (hR : (R.subgroupOf X).IsCComponent)
    (S : Sylow 2 G) (hSX : (S : Subgroup G) ≤ X) :
    X ≤ normalizer (conjugateSpanBy R (S : Subgroup G) : Set G) := by
  let Q := S.subtype hSX
  let J := conjugateSpanBy (R.subgroupOf X) (Q : Subgroup X)
  let : J.Normal := conjugateSpanBy_sylow_normal _ Q
    (Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ hR)
  have he : J.map X.subtype = conjugateSpanBy R (S : Subgroup G) := by
    rw [map_conjugateSpanBy,map_subgroupOf_eq_of_le hRX]
    change conjugateSpanBy R (((S : Subgroup G).subgroupOf X).map X.subtype) = _
    rw [map_subgroupOf_eq_of_le hSX]
  have hn := J.le_normalizer_map X.subtype
  rw [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype,he] at hn
  exact hn

/-- In the larger-Sylow branch R cannot already be a C-component of
the common overgroup. Its two Sylow orbit spans would coincide and be normal,
contradicting the marked conjugate escape. -/
theorem LocalData.changedSylow_not_common_component
    {T U : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    (hU : (U : Subgroup G) =
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    ¬ (R.subgroupOf (normalizer (normalizingSylow T R : Set G) ⊔ H)).IsCComponent := by
  intro hR
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  have hRX : R ≤ X := d.right_le_residual.trans ((map_subtype_le _).trans le_sup_right)
  have hTX : (T : Subgroup G) ≤ X := (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hTU : normalizingSylow T R ≤ (U : Subgroup G) := hTP.trans_eq hU.symm
  have hUX : (U : Subgroup G) ≤ X :=
    (d.overgroup_two_subgroup_normalizes hH.1.1.2 c hd hz U.isPGroup' hTU).trans le_sup_left
  have hQ := Chapter3.sqtk_of_mem_H h.qtke (d.common_normal_overgroup h hH c hd hz).1
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_,hQ.isKGroup.quotient _⟩
    intro q hq ho
    let : Fact q.Prime := ⟨hq⟩
    exact (primeRank_quotient_le_of_isTwoGroup q ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin q hq ho)
  have hNK := component_sylow_orbit_normalizes hRX hQbar hR T hTX
  rw [←d.residual_eq_conjugateSpan] at hNK
  have hNK₀ := component_sylow_orbit_normalizes hRX hQbar hR U hUX
  have hKK₀ : residual H ≤ conjugateSpanBy R (U : Subgroup G) := by
    rw [d.residual_eq_conjugateSpan]
    exact conjugateSpanBy_le (le_conjugateSpanBy _ _) (hTX.trans hNK₀)
  have hK₀E : conjugateSpanBy R (U : Subgroup G) ≤ extension T L H B D R :=
    conjugateSpanBy_le
      (le_sup_left.trans (le_sup_right.trans (le_sup_left.trans le_sup_left)))
      ((hU ▸ map_subtype_le _).trans (extension T L H B D R).le_normalizer)
  obtain ⟨x,hxN,_,_,hxD,hxT⟩ := d.changedSylow_marked_conjugator h hH c hd hz hTU
  have hxK := mem_normalizer_iff_map_conj_eq.mp (hNK (mem_sup_left hxN))
  apply d.changedSylow_conjugate_outside hd hz P hU hxD hxT
  exact ((map_mono (f := (MulAut.conj x).toMonoidHom) d.right_le_residual).trans_eq hxK).trans
    (hKK₀.trans hK₀E)

/-- Local maximality of the original right factor excludes every larger
changed Sylow. Source 1.2.8(3) supplies this premise for moved non-A₅ local
components; construction of that source input remains separate. -/
theorem LocalData.changedSylow_eq_of_right_maximal
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hR : R ∈ Chapter1.LStar G (T : Subgroup G))
    (P : Sylow 2 (extension T L H B D R))
    (hTP : normalizingSylow T R ≤
      (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype) :
    (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype =
      normalizingSylow T R := by
  have hcases := (two_group_over_index_two_sylow T (normalizingSylow T R)
    ((P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype)
    inf_le_left (d.normalizingSylow_index hH.1.1.2 c hd hz) (P.isPGroup'.map _) hTP).2
  rcases hcases with he | ⟨U,hU⟩
  · exact he
  · exfalso
    let X := normalizer (normalizingSylow T R : Set G) ⊔ H
    have hX := d.common_normal_overgroup h hH c hd hz
    have hTX : (T : Subgroup G) ≤ X :=
      (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
    obtain ⟨I,hRI,hIX,hI,_⟩ := d.common_normal_component h hH c hd hz
    have hIl : I ∈ Chapter1.L G (T : Subgroup G) :=
      Chapter1.mem_L_of_cComponent hX.1
        ⟨T.subtype hTX,map_subgroupOf_eq_of_le hTX⟩ hIX hI
    have he : I = R := hR.2 I hIl hRI
    apply d.changedSylow_not_common_component h hH c hd hz P hTP hU
    simpa only [he] using hI

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
