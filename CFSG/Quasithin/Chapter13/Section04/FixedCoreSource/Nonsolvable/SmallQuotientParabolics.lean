module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.ParabolicComparison
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoKernel
public import Theory.GroupTheory.SylowIndexThreeQuotient
public import Theory.GroupTheory.PResidual.TwoThreeComparison

/-!
# Parabolics in all three nonsolvable centralizer quotient rows

Lift the L₃(2), A₆ and S₆ Sylow intervals through the literal two-core
quotient of the original centralizer. The inside parabolic determines the
unique outside member of H*(T,M), including its maximality, solvability,
intersection, generation and fixed residual line. Its Sylow index is three;
the earlier Sylow-normalizer containment then identifies P/O₂(P) with S₃.
The same index calculation proves that P is a {2,3}-group and hence
O²(P)=O^{3′}(P), retaining the source residual convention.

The source component K, the quotient recognition, the inside parabolic,
and full Ω₁Z(T) containment remain obligations of qt-d-1341-nonsolvable-source.
These are constructions from explicit local model inputs, not a proof of
13.4.10 or the full nonsolvable branch. Earlier Chapter12 and local inputs
retain final discharge with qt-d-1341-fixed-core-source.

Source: Aschbacher–Smith 13.4.10(7) and 13.4.7 applicability, pp.909–911.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem small_quotient_pair (N : Subgroup G) (S : Sylow 2 N)
    (model : Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 6))) :
    ∃ P Q : Subgroup N,
      IsCoatom P ∧ IsCoatom Q ∧ P ≠ Q ∧ P ⊓ Q = (S : Subgroup N) ∧
      (S : Subgroup N) < P ∧ (S : Subgroup N) < Q ∧
      Group.IsSolvable P ∧ Group.IsSolvable Q ∧
      ∀ U : Subgroup N, (S : Subgroup N) ≤ U →
        U = (S : Subgroup N) ∨ U = P ∨ U = Q ∨ U = ⊤ := by
  rcases model with hmodel | hmodel | hmodel
  · obtain ⟨e⟩ := hmodel
    let f : N →* Matrix.PSL3Two.PSL :=
      (e.trans Matrix.PSL3Two.equiv).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
    have hf : Function.Surjective f :=
      (e.trans Matrix.PSL3Two.equiv).surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 f.ker := by
      have he : f.ker = pCore 2 N := by
        ext x
        change (e.trans Matrix.PSL3Two.equiv) (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
        rw [(e.trans Matrix.PSL3Two.equiv).map_eq_one_iff]
        exact QuotientGroup.eq_one_iff x
      rw [he]
      exact pCore_isPGroup
    exact Matrix.PSL3Two.two_kernel_parabolics S f hf hk
  · obtain ⟨e⟩ := hmodel
    let f : N →* alternatingGroup (Fin 6) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 f.ker := by
      have he : f.ker = pCore 2 N := by
        ext x
        change e (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
        rw [e.map_eq_one_iff]
        exact QuotientGroup.eq_one_iff x
      rw [he]
      exact pCore_isPGroup
    exact Theory.SpecificGroups.SymmetricSix.alternating_two_kernel_parabolics
      S f hf hk
  · obtain ⟨e⟩ := hmodel
    let f : N →* Equiv.Perm (Fin 6) :=
      e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 f.ker := by
      have he : f.ker = pCore 2 N := by
        ext x
        change e (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
        rw [e.map_eq_one_iff]
        exact QuotientGroup.eq_one_iff x
      rw [he]
      exact pCore_isPGroup
    exact Theory.SpecificGroups.SymmetricSix.symmetric_two_kernel_parabolics
      S f hf hk

/-- The unique outside parabolic for all three literal quotient models. -/
theorem small_quotient_unique_outside
    (T : Sylow 2 G) (M N A : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hN : N ∈ Chapter1.HOver G (T : Set G)) (hNM : ¬ N ≤ M)
    (hTA : (T : Subgroup G) < A) (hAN : A < N) (hAM : A ≤ M)
    (model : Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 6))) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) M ∧ P < N ∧
      Group.IsSolvable P ∧ A ⊔ P = N ∧ A ⊓ P = (T : Subgroup G) ∧
      (∀ U ∈ Chapter3.HStar (T : Subgroup G) M, U ≤ N → U = P) := by
  exact unique_outside_of_sylow_pair T M N A hTM hN hNM hTA hAN hAM
    (small_quotient_pair N (T.subtype hN.2) model)

open Chapter12.Section02 Chapter14.Section03.FaithfulSource
variable {T : Sylow 2 G} {L V : Subgroup G} {D : ChosenModule T L V}

/-- Every proper strict Sylow overgroup in the three recognized rows is
maximal in the actual ambient overgroup. -/
theorem small_quotient_parabolic_maximal
    (N P : Subgroup G) (hTP : (T : Subgroup G) < P) (hPN : P < N)
    (model : Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 6))) : P ⋖ N := by
  let S := T.subtype (hTP.le.trans hPN.le)
  have hS : (S : Subgroup N).map N.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (hTP.le.trans hPN.le)
  have hP : (P.subgroupOf N).map N.subtype = P := map_subgroupOf_eq_of_le hPN.le
  have htop : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨A, B, hA, hB, _, _, _, _, _, _, cover⟩ := small_quotient_pair N S model
  have hc : IsCoatom (P.subgroupOf N) := by
    rcases cover (P.subgroupOf N) (fun _ hx => hTP.le hx) with he | he | he | he
    · have hh := congrArg (fun U : Subgroup N => U.map N.subtype) he
      rw [hP, hS] at hh
      exact (hTP.ne hh.symm).elim
    · exact he ▸ hA
    · exact he ▸ hB
    · have hh := congrArg (fun U : Subgroup N => U.map N.subtype) he
      rw [hP, htop] at hh
      exact (hPN.ne hh).elim
  refine ⟨hPN, ?_⟩
  intro U hPU hUN
  have hPU' : P.subgroupOf N < U.subgroupOf N := by
    refine lt_of_le_of_ne (subgroupOf_mono N hPU.le) ?_
    intro he
    have hh := congrArg (fun U : Subgroup N => U.map N.subtype) he
    rw [hP, map_subgroupOf_eq_of_le hUN.le] at hh
    exact hPU.ne hh
  have hh := congrArg (fun U : Subgroup N => U.map N.subtype) (hc.2 _ hPU')
  rw [map_subgroupOf_eq_of_le hUN.le, htop] at hh
  exact hUN.ne hh


private theorem linear_sylow_parabolic_index
    (S : Sylow 2 Matrix.PSL3Two.PSL) (U : Subgroup Matrix.PSL3Two.PSL)
    (hSU : (S : Subgroup Matrix.PSL3Two.PSL) < U) (hU : U ≠ ⊤) :
    (S : Subgroup Matrix.PSL3Two.PSL).relIndex U = 3 := by
  obtain ⟨P, Q, _, _, _, _, hP, hQ, hmax⟩ := Matrix.PSL3Two.sylow_parabolics S
  obtain ⟨R, hR, hUR⟩ := (eq_top_or_exists_le_coatom U).resolve_left hU
  have hd : Nat.card U ∣ 24 := by
    rcases (hmax R hR).mp (hSU.le.trans hUR) with he | he
    · simpa only [he, hP] using card_dvd_of_le hUR
    · simpa only [he, hQ] using card_dvd_of_le hUR
  have h8 : 8 ∣ Nat.card U := Matrix.PSL3Two.card_sylow_two S ▸ card_dvd_of_le hSU.le
  have hne : Nat.card U ≠ 8 := by
    intro he
    exact hSU.ne (eq_of_le_of_card_ge hSU.le (by rw [he, Matrix.PSL3Two.card_sylow_two]))
  have hb := Nat.le_of_dvd (by decide : 0 < 24) hd
  have hc : Nat.card U = 24 := by
    interval_cases hu : Nat.card U <;> omega
  have hm := (S : Subgroup Matrix.PSL3Two.PSL).subgroupOf U |>.card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hSU.le).toEquiv,
    Matrix.PSL3Two.card_sylow_two, hc] at hm
  change 8 * (S : Subgroup Matrix.PSL3Two.PSL).relIndex U = 24 at hm
  omega

private theorem parabolic_index_lift {X Y : Type*} [Group X] [Group Y] [Finite X]
    (S : Sylow 2 X) (f : X →* Y) (hf : Function.Surjective f)
    (hk : IsPGroup 2 f.ker)
    (index : ∀ (R : Sylow 2 Y) (U : Subgroup Y), (R : Subgroup Y) < U → U ≠ ⊤ →
      (R : Subgroup Y).relIndex U = 3)
    (P : Subgroup X) (hSP : (S : Subgroup X) < P) (hP : P ≠ ⊤) :
    (S : Subgroup X).relIndex P = 3 := by
  have hker := hk.le_sylow_of_normal S
  have hS : ((S : Subgroup X).map f).comap f = (S : Subgroup X) :=
    comap_map_eq_self hker
  have hPc : (P.map f).comap f = P := comap_map_eq_self (hker.trans hSP.le)
  have hSP' : ((S.mapSurjective hf : Sylow 2 Y) : Subgroup Y) < P.map f := by
    refine lt_of_le_of_ne (map_mono hSP.le) ?_
    intro he
    have hh := congrArg (comap f) he
    change ((S : Subgroup X).map f).comap f = (P.map f).comap f at hh
    rw [hS, hPc] at hh
    exact hSP.ne hh
  have hP' : P.map f ≠ ⊤ := by
    intro he
    rw [← hPc, he, comap_top] at hP
    exact hP rfl
  have hi := index (S.mapSurjective hf) (P.map f) hSP' hP'
  change ((S : Subgroup X).map f).relIndex (P.map f) = 3 at hi
  rwa [relIndex_map_map, sup_eq_left.mpr hker,
    sup_eq_left.mpr (hker.trans hSP.le)] at hi

/-- The actual parabolics in each of the three quotient rows have Sylow index three. -/
theorem small_quotient_parabolic_index
    (N P : Subgroup G) (hTP : (T : Subgroup G) < P) (hPN : P < N)
    (model : Nonempty ((N ⧸ pCore 2 N) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((N ⧸ pCore 2 N) ≃* Equiv.Perm (Fin 6))) :
    (T : Subgroup G).relIndex P = 3 := by
  let S := T.subtype (hTP.le.trans hPN.le)
  have hSP : (S : Subgroup N) < P.subgroupOf N := by
    refine lt_of_le_of_ne (fun _ hx => hTP.le hx) ?_
    intro he
    have hh := congrArg (fun U : Subgroup N => U.map N.subtype) he
    change ((T : Subgroup G).subgroupOf N).map N.subtype =
      (P.subgroupOf N).map N.subtype at hh
    rw [map_subgroupOf_eq_of_le (hTP.le.trans hPN.le),
      map_subgroupOf_eq_of_le hPN.le] at hh
    exact hTP.ne hh
  have hP : P.subgroupOf N ≠ ⊤ := by
    intro he
    have hh := congrArg (fun U : Subgroup N => U.map N.subtype) he
    rw [map_subgroupOf_eq_of_le hPN.le, ← MonoidHom.range_eq_map, range_subtype] at hh
    exact hPN.ne hh
  have finish {Y : Type} [Group Y] (e : (N ⧸ pCore 2 N) ≃* Y)
      (index : ∀ (R : Sylow 2 Y) (U : Subgroup Y), (R : Subgroup Y) < U → U ≠ ⊤ →
        (R : Subgroup Y).relIndex U = 3) : (T : Subgroup G).relIndex P = 3 := by
    let f : N →* Y := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 N))
    have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
    have hk : IsPGroup 2 f.ker := by
      have he : f.ker = pCore 2 N := by
        ext x
        change e (QuotientGroup.mk' (pCore 2 N) x) = 1 ↔ _
        rw [e.map_eq_one_iff]
        exact QuotientGroup.eq_one_iff x
      rw [he]
      exact pCore_isPGroup
    have hi := parabolic_index_lift S f hf hk index (P.subgroupOf N) hSP hP
    change ((T : Subgroup G).subgroupOf N).relIndex (P.subgroupOf N) = 3 at hi
    rwa [relIndex_subgroupOf hPN.le] at hi
  rcases model with he | he | he
  · obtain ⟨e⟩ := he
    exact finish (e.trans Matrix.PSL3Two.equiv) linear_sylow_parabolic_index
  · obtain ⟨e⟩ := he
    exact finish e Theory.SpecificGroups.SymmetricSix.alternating_sylow_parabolic_index
  · obtain ⟨e⟩ := he
    exact finish e Theory.SpecificGroups.SymmetricSix.symmetric_sylow_parabolic_index

/-- The original Sylow-normalizer containment excludes a normal Sylow subgroup
in the escaping parabolic, so its literal two-core quotient is S₃. -/
theorem escaping_parabolic_quotient_and_residual
    (P : Subgroup G)
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hi : (T : Subgroup G).relIndex P = 3) :
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      pResidual 2 P = primeToResidual 3 P := by
  let S := T.subtype hP.1.1.2
  have hS : (S : Subgroup P).map P.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hP.1.1.2
  have hproper : pCore 2 P < (S : Subgroup P) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S) ?_
    intro he
    have hn : P ≤ normalizer (P.pCoreIn 2 : Set G) := by
      simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using
        (pCore 2 P).le_normalizer_map P.subtype
    have hcore : P.pCoreIn 2 = (T : Subgroup G) := by
      change (pCore 2 P).map P.subtype = _
      rw [he, hS]
    rw [hcore] at hn
    exact hP.1.2 (hn.trans hNT)
  have hindex : (S : Subgroup P).index = 3 := hi
  refine ⟨sylow_index_three_core_quotient S hindex hproper, ?_⟩
  apply twoResidual_eq_primeToResidual_three
  rw [IsPiGroup_iff]
  intro q hq
  have hc := (S : Subgroup P).card_mul_index
  obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
  rw [hindex, hn] at hc
  rw [← hc] at hq
  change q.val = 2 ∨ q.val = 3
  rcases q.property.dvd_mul.mp hq with hq | hq
  · exact Or.inl ((Nat.dvd_prime Nat.prime_two).mp
      (q.property.dvd_of_dvd_pow hq) |>.resolve_left q.property.ne_one)
  · exact Or.inr ((Nat.dvd_prime Nat.prime_three).mp hq |>.resolve_left q.property.ne_one)

/-- Construct the unique parabolic in an escaping centralizer, including its
solvability, fixed residual line and the literal index required by 13.4.7. -/
theorem small_quotient_centralizer_parabolic
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (m : CoreMarking D) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (A : Subgroup G) (hTA : (T : Subgroup G) < A)
    (hAC : A < centralizer ({z.val} : Set G)) (hAM : A ≤ normalizer (L : Set G))
    (model : Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* Equiv.Perm (Fin 6))) :
    ∃ P : Subgroup G,
      P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)) ∧
      ChapterB.IsMinimalParabolicOver T P ∧
      P < centralizer ({z.val} : Set G) ∧ Group.IsSolvable P ∧
      A ⊔ P = centralizer ({z.val} : Set G) ∧ A ⊓ P = (T : Subgroup G) ∧
      centralizer (pCore 2 P : Set P) ≤ pCore 2 P ∧
      (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
        centralizer ((pResidual 2 P).map P.subtype : Set G) = zpowers z.val ∧
      ((V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) ⊓
        centralizer ((pResidual 2 P).map P.subtype : Set G)).relIndex
          (V ⊓ Stellmacher.omegaOneCenterAmbient (T : Subgroup G)) = 2 ∧
      (∀ U ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
        U ≤ centralizer ({z.val} : Set G) → U = P) ∧
      P ⋖ centralizer ({z.val} : Set G) ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      pResidual 2 P = primeToResidual 3 P := by
  obtain ⟨P, hP, hPC, hs, hgen, hi, hu⟩ := small_quotient_unique_outside T _ _ A
    D.sylow_normalizes_component
    (Solvable.centralizer_mem_HOver hzT (fun he => hz1 (Subtype.ext he)))
    hzout hTA hAC hAM model
  have hTP : (T : Subgroup G) < P := lt_of_le_of_ne hP.1.1.2 (by
    intro he
    exact hP.1.2 (he ▸ D.sylow_normalizes_component))
  have hidx := small_quotient_parabolic_index _ P hTP hPC model
  have hquot := escaping_parabolic_quotient_and_residual P hP hNT hidx
  exact ⟨P, hP, Chapter3.HStar.minimalParabolic T D.sylow_normalizes_component hP
      (Or.inl hNT), hPC, hs, hgen, hi,
    Chapter1.mem_He_iff.mp
      (Chapter1.lemma_1_1_4_6 T (h₀.qtke.evenCharacteristic T) hP.1.1),
    escaping_residual_fixed_line h structural m z hz1 hzT P hP hPC.le,
    escaping_residual_fixed_index h structural m z hz1 hzT P hP hPC.le, hu,
    small_quotient_parabolic_maximal _ P hTP hPC model, hquot.1, hquot.2⟩

/-- Any minimal outside subgroup of a recognized centralizer is its constructed
solvable parabolic. This discharges `four_solvable` in the comparison. -/
theorem escaping_parabolic_solvable_of_small_quotient
    (D : ChosenModule T L V) (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (A P : Subgroup G) (hTA : (T : Subgroup G) < A)
    (hAC : A < centralizer ({z.val} : Set G)) (hAM : A ≤ normalizer (L : Set G))
    (hP : P ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hPz : P ≤ centralizer ({z.val} : Set G))
    (model : Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃*
          Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((centralizer ({z.val} : Set G) ⧸
        pCore 2 (centralizer ({z.val} : Set G))) ≃* Equiv.Perm (Fin 6))) :
    Group.IsSolvable P := by
  obtain ⟨Q, _, _, hs, _, _, hu⟩ := small_quotient_unique_outside T _ _ A
    D.sylow_normalizes_component
    (Solvable.centralizer_mem_HOver hzT (fun he => hz1 (Subtype.ext he)))
    (fun hh => hP.1.2 (hPz.trans hh)) hTA hAC hAM model
  exact (hu P hP hPz).symm ▸ hs


end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
