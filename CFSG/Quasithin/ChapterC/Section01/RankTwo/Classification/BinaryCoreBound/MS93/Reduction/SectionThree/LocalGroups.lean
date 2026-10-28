module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.ModuleFacts
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.Frattini.PGroup

/-!
# Local groups for the binary Section 3 reduction

Positive critical distance puts Z and its moving subgroup U in the elementary
omega-center of Q. Coprime commutator idempotence inside the finite vertex
stabilizer proves [U,Ltilde] = U without identifying U as a natural module.
At distance greater than two the entire radius-two group V lies in Q:
its M-vertex generators lie there by critical minimality, and its H-vertex
generators already lie in Z. The actual local kernels have a common order.

The final lemma converts the two source (3.6) alternatives into abelianness.
It takes the dichotomy explicitly; it does not prove (3.6). Neither the
natural-module identification nor X = Z is assumed by the other results.
All finiteness arguments concern local stabilizers, not the free amalgam.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (2.1)--(2.2), (3.6), (4.1)--(4.2), printed pp.855--857, 870--872,
881--882. The fixed/moving decomposition and Section 3 classification
remain separate obligations.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] {L R : Subgroup M}

theorem Ltilde_le_stabilizer (a : Vertex R) : Ltilde R a ≤ stabilizer R a :=
  map_subtype_le _

theorem U_le_Z (a : Vertex R) : U R a ≤ Z R a :=
  le_normalizer_iff_commutator_le_left.mp
    ((Ltilde_le_stabilizer a).trans (Z_normalized R a))

theorem V_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (V R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (V R a).map (MulAut.conj g).toMonoidHom = V R a
  have h := V_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

theorem U_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (U R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (U R a).map (MulAut.conj g).toMonoidHom = U R a
  have h := U_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

theorem Vcirc_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (Vcirc R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (Vcirc R a).map (MulAut.conj g).toMonoidHom = Vcirc R a
  have h := Vcirc_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using h.symm

theorem Geometry.Z_elementary (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : IsElementaryAbelian 2 (Z R a) := by
  let : IsElementaryAbelian 2 (X R a) := omegaCenter_elementary (Q R a)
  have h := geometry.omega_bound a ha (by rwa [geometry.distance_constant a ha])
  exact IsElementaryAbelian.of_le h

theorem Geometry.U_elementary (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : IsElementaryAbelian 2 (U R a) := by
  let := geometry.Z_elementary hb a ha
  exact IsElementaryAbelian.of_le (U_le_Z a)

theorem Q_le_stabilizer_of_dist_le_two [Finite M] (a c : Vertex R)
    (ha : color R a = false) (hc : color R c = false)
    (hd : (cosetGraph R).dist a c ≤ 2) : Q R a ≤ stabilizer R c := by
  obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a c
  cases p with
  | nil => exact fun _ hx => hx.1
  | @cons a t c hat p =>
    have hat' := (cosetGraph_adj R _ _).mp hat
    have ht : color R t = true := by
      have h := adjacent_color_ne R hat'
      cases hcol : color R t <;> simp_all
    cases p with
    | nil => rw [hc] at ht; cases ht
    | @cons t s c hts p =>
      have hlen : p.length = 0 := by simp only [SimpleGraph.Walk.length_cons] at hp; omega
      have hsc : s = c := p.eq_of_length_eq_zero hlen
      subst s
      intro x hx
      exact (Q_le_adjacent_h R ht hat' hx).2 c ((cosetGraph_adj R _ _).mp hts)

theorem Geometry.V_le_Q [Finite M] (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : V R a ≤ Q R a := by
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  by_cases hc : color R t = false
  · apply Z_le_Q_of_dist_lt R t (geometry.exists_critical t hc)
    rw [geometry.distance_constant t hc]
    exact lt_of_le_of_lt ht hb
  · have hc' : color R t = true := by cases hh : color R t <;> simp_all
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist t a
    have hnEven : ¬ Even p.length := by
      rw [walk_even_iff_color_eq, hc', ha]
      decide
    have hlen : p.length = 1 := by
      have hle : p.length ≤ 2 := hp.trans_le ht
      rw [Nat.even_iff] at hnEven
      omega
    have hadj : Adjacent R a t :=
      adjacent_symm R ((cosetGraph_adj R _ _).mp (p.adj_of_length_eq_one hlen))
    have htZ : Z R t ≤ Z R a := by
      rw [Z, if_neg hc, Z, if_pos ha]
      exact le_iSup_of_le t (le_iSup_of_le hadj le_rfl)
    exact htZ.trans ((geometry.omega_bound a ha
      (by rw [geometry.distance_constant a ha]; change 0 < geometry.b R; omega)).trans (omegaCenter_le _))

private theorem finite_stabilizer_m [Finite M] (a : Vertex R) (ha : color R a = false) :
    Finite (stabilizer R a) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have : Finite (Mbar R) := Finite.of_surjective (embedM R).rangeRestrict
    (embedM R).rangeRestrict_surjective
  rw [stabilizer_mVertex]
  exact Finite.of_equiv (Mbar R)
    ((Mbar R).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).toEquiv

theorem Geometry.U_full_commutation [Finite M] (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false) :
    ⁅U R a, Ltilde R a⁆ = U R a := by
  let S := stabilizer R a
  let A := (Z R a).subgroupOf S
  let : Finite S := finite_stabilizer_m a ha
  let : A.Normal := geometry.Z_normal a
  let : IsElementaryAbelian 2 (Z R a) := geometry.Z_elementary hb a ha
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.subgroupOf (Z_le_stabilizer R a)
  have h := commutator_isPPerfect_idempotent (pResidual 2 S) A
    (isPPerfect_pResidual 2) (IsElementaryAbelian.isPGroup 2 A) le_normalizer_of_normal
  have hh := congrArg (Subgroup.map S.subtype) h
  have hA : A.map S.subtype = Z R a :=
    map_subgroupOf_eq_of_le (Z_le_stabilizer R a)
  simp only [map_commutator, hA] at hh
  exact hh

private theorem LocalSource.Q_isPGroup [Finite M] (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) : IsPGroup 2 (Q R a) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have h := Q_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at h
  rw [h]
  have hbase : IsPGroup 2 (Q R (alpha R)) := by
    rw [Q_alpha R source.two_group source.core_le]
    exact pCore_isPGroup.map (embedM R)
  exact hbase.map _

theorem LocalSource.Q_card [Finite M] (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) : Nat.card (Q R a) = Nat.card (pCore 2 M) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have h := Q_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at h
  rw [h, ← Nat.card_congr ((Q R (mVertex R 1)).equivMapOfInjective
    (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective).toEquiv]
  change Nat.card (Q R (alpha R)) = _
  rw [Q_alpha R source.two_group source.core_le]
  exact (Nat.card_congr ((pCore 2 M).equivMapOfInjective (embedM R)
    (embedM_injective R)).toEquiv).symm

theorem LocalSource.V_isPGroup [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : 2 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) : IsPGroup 2 (V R a) :=
  (source.Q_isPGroup a ha).to_le (geometry.V_le_Q hb a ha)

theorem LocalSource.X_centralizer [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false) :
    stabilizer R a ⊓ centralizer (X R a : Set (FreeAmalgam R)) = Q R a := by
  have hZX : Z R a ≤ X R a := geometry.omega_bound a ha
    (by rw [geometry.distance_constant a ha]; exact hb)
  apply le_antisymm
  · calc
      stabilizer R a ⊓ centralizer (X R a : Set (FreeAmalgam R)) ≤ C R a :=
        inf_le_inf_left _ (centralizer_le hZX)
      _ = Q R a := source.C_eq_Q geometry.radical_ne_bot a ha
  · intro q hq
    refine ⟨hq.1, ?_⟩
    intro x hx
    exact ((mem_omegaCenter_iff.mp hx).2.2 q hq).symm

theorem Geometry.core_commutative_of_eq_U (geometry : Geometry R)
    (hb : 0 < geometry.b R) (a : Vertex R) (ha : color R a = false)
    (hcore : core R a = U R a) : IsMulCommutative (core R a) := by
  rw [hcore]
  exact (geometry.U_elementary hb a ha).toIsMulCommutative

/-- The two alternatives asserted in (3.6) both make the core abelian.
The dichotomy itself is an explicit remaining premise. -/
theorem LocalSource.core_commutative_of_b_two_alternative [Finite M]
    (source : LocalSource L R) (geometry : Geometry R) (hb : geometry.b R = 2)
    (halt : core R (alpha R) = U R (alpha R) ∨ frattini (core R (alpha R)) = ⊥) :
    IsMulCommutative (core R (alpha R)) := by
  rcases halt with h | h
  · exact geometry.core_commutative_of_eq_U (by omega) (alpha R) rfl h
  · have hcore := core_alpha R source.two_group source.core_le source.residual
    have hcQ : core R (alpha R) ≤ Q R (alpha R) := by
      rw [hcore, Q_alpha R source.two_group source.core_le]
      exact map_mono (commutator_le_left _ _)
    let : Finite (stabilizer R (alpha R)) := finite_stabilizer_m (alpha R) rfl
    let : Finite (core R (alpha R)) := Finite.of_injective
      (inclusion (hcQ.trans (fun _ hx => hx.1))) (inclusion_injective _)
    let : Fact (IsPGroup 2 (core R (alpha R))) :=
      ⟨(source.Q_isPGroup (alpha R) rfl).to_le hcQ⟩
    exact ((frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp h).toIsMulCommutative

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
