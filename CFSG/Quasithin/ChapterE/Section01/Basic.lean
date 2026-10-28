module

public import CFSG.Quasithin.ChapterE.Defs

/-!
# Elementary properties of E-generation

We establish the first containment in E.1.8(1), the quotient-centralizer
identity used in E.1.8(3), monotonicity in the rank bound, and the elementary
minimum specifications for E.1.6. A positive parameter supplies an attained
minimum and hence a generation witness, including the escaping E-member used
in F.7.13. General existence for even-order groups remains a separate theorem.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
E.1.1--E.1.8, pp.209--211.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterE
open Subgroup
variable {G : Type*} [Group G]

theorem tau_le (T A : Subgroup G) : tau T A ≤ T := centralizerModulo_le _ _ _

/-- The source inclusion `A O₂(G) ≤ τ(G,T,A)`. -/
theorem sup_pCore_le_tau (T : Sylow 2 G) (A : Subgroup G)
    [IsElementaryAbelian 2 A] (hAT : A ≤ (T : Subgroup G)) :
    A ⊔ pCore 2 G ≤ tau (T : Subgroup G) A := by
  apply sup_le
  · exact le_centralizerModulo_of_isMulCommutative hAT
  · have hcore : pCore 2 G ≤ (T : Subgroup G) := pCore_isPGroup.le_sylow_of_normal T
    simpa only [tau, inf_eq_right.mpr hcore] using
      inf_le_centralizerModulo (T : Subgroup G) A (pCore 2 G)

/-- E.1.8(1): tau passes into the intrinsic tau of an overgroup containing it. -/
theorem tau_le_map_tau (T A H : Subgroup G)
    (hH : tau T A ≤ H) :
    tau T A ≤ (tau (T.subgroupOf H)
      (A.subgroupOf H)).map H.subtype := by
  have hcore : (pCore 2 G).subgroupOf H ≤ pCore 2 H :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  intro x hx
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
  refine ⟨⟨x, hH hx⟩, ?_, rfl⟩
  apply mem_centralizerModulo_iff.mpr
  exact ⟨hxT, fun a ha => hcore (hc a ha)⟩

/-- Kernel-intersection form of the centralizer equality in E.1.8(3). -/
theorem centralizerModulo_eq_tau {T A Y : Subgroup G} [Y.Normal]
    (hAT : A ≤ T) (hTY : T ⊓ Y = pCore 2 G) :
    centralizerModulo T A Y = tau T A := by
  apply centralizerModulo_eq_of_inf_eq hAT
  have hcore : pCore 2 G ≤ T := hTY ▸ inf_le_left
  rw [hTY, inf_eq_right.mpr hcore]

/-- Under the source Sylow hypothesis, `T ∩ Y = O₂(G)`. -/
theorem inf_eq_pCore_of_sylow (T : Sylow 2 G) (Y : Subgroup G)
    (P : Sylow 2 Y) (hP : (P : Subgroup Y).map Y.subtype = pCore 2 G) :
    (T : Subgroup G) ⊓ Y = pCore 2 G := by
  have hle : (P : Subgroup Y) ≤ (T : Subgroup G).subgroupOf Y := by
    apply map_le_iff_le_comap.mp
    rw [hP]
    exact pCore_isPGroup.le_sylow_of_normal T
  have heq := P.is_maximal' T.isPGroup'.comap_subtype hle
  have hm := congrArg (fun U : Subgroup Y => U.map Y.subtype) heq
  change ((T : Subgroup G).subgroupOf Y).map Y.subtype =
    (P : Subgroup Y).map Y.subtype at hm
  simpa only [subgroupOf_map_subtype, inf_comm, hP] using hm

/-- E.1.8(3), first clause, with the Sylow subgroup of `Y` exhibited explicitly. -/
theorem tau_eq_quotientCentralizer (T : Sylow 2 G) (A Y : Subgroup G) [Y.Normal]
    (hAT : A ≤ (T : Subgroup G)) (P : Sylow 2 Y)
    (hP : (P : Subgroup Y).map Y.subtype = pCore 2 G) :
    centralizerModulo (T : Subgroup G) A Y = tau (T : Subgroup G) A :=
  centralizerModulo_eq_tau hAT (inf_eq_pCore_of_sylow T Y P hP)

/-- E.1.8(3), the image of tau is contained in tau in the quotient. -/
theorem map_tau_le_quotient_tau (T : Sylow 2 G) (A Y : Subgroup G) [Y.Normal]
    (hAT : A ≤ (T : Subgroup G)) (P : Sylow 2 Y)
    (hP : (P : Subgroup Y).map Y.subtype = pCore 2 G) :
    (tau (T : Subgroup G) A).map (QuotientGroup.mk' Y) ≤
      tau ((T : Subgroup G).map (QuotientGroup.mk' Y)) (A.map (QuotientGroup.mk' Y)) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← tau_eq_quotientCentralizer T A Y hAT P hP] at hx
  obtain ⟨hxT, hc⟩ := mem_centralizerModulo_iff.mp hx
  apply mem_centralizerModulo_iff.mpr
  refine ⟨mem_map_of_mem _ hxT, ?_⟩
  rintro _ ⟨a, ha, rfl⟩
  rw [← map_commutatorElement]
  have he := (QuotientGroup.eq_one_iff _).mpr (hc a ha)
  change (QuotientGroup.mk' Y) _ = 1 at he
  rw [he]
  exact (pCore 2 (G ⧸ Y)).one_mem

variable [Finite G]

theorem IsEMemberAt.mono {i j : ℕ} {T A K : Subgroup G}
    (h : IsEMemberAt i T A K) (hij : i ≤ j) : IsEMemberAt j T A K := by
  refine ⟨h.1, ?_⟩
  rcases h.2 with h | h
  · exact Or.inl ⟨h.1, h.2.trans hij⟩
  · exact Or.inr ⟨h.1, h.2.trans hij⟩

theorem eSubgroup_mono {i j : ℕ} (T A : Subgroup G) (hij : i ≤ j) :
    eSubgroup i T A ≤ eSubgroup j T A := by
  apply sSup_le_sSup
  intro K hK
  exact hK.mono hij

theorem eFamilySubgroup_mono {i j : ℕ} (T : Subgroup G) (Ω : Set (Subgroup G))
    (hij : i ≤ j) : eFamilySubgroup i T Ω ≤ eFamilySubgroup j T Ω :=
  iSup_mono fun A => eSubgroup_mono T A.1 hij

omit [Finite G] in
theorem weakClosure_le (T : Subgroup G) (Ω : Set (Subgroup G)) :
    weakClosure T Ω ≤ T := sSup_le fun _ h => h.2

omit [Finite G] in
/-- Restriction to an overgroup of `T` does not change the weak closure in `T`.
This is the elementary normalizer step in E.1.11 and E.1.12. -/
theorem weakClosure_restrict {T H : Subgroup G} (hTH : T ≤ H)
    (Ω : Set (Subgroup G)) :
    weakClosure T {A | A ∈ Ω ∧ A ≤ H} = weakClosure T Ω := by
  unfold weakClosure
  congr 1
  ext A
  exact ⟨fun h => ⟨h.1.1, h.2⟩, fun h => ⟨⟨h.1, h.2.trans hTH⟩, h.2⟩⟩

theorem IsEGeneratedAt.mono {i j : ℕ} {T : Sylow 2 G}
    (h : IsEGeneratedAt i T) (hij : i ≤ j) : IsEGeneratedAt j T := by
  intro Ω hΩ
  apply top_unique
  rw [← h Ω hΩ]
  exact sup_le_sup_right (eFamilySubgroup_mono _ _ hij) _

theorem IsEGenerated.mono {i j : ℕ} (h : IsEGenerated i G) (hij : i ≤ j) :
    IsEGenerated j G := fun T => (h T).mono hij

theorem generationParameter_eq_zero_of_odd (h : Odd (Nat.card G)) :
    generationParameter G = 0 := if_pos h

/-- A positive generation bound bounds the minimum, without requiring a
separate general existence theorem. -/
theorem generationParameter_le {i : ℕ} (hi : 0 < i) (h : IsEGenerated i G) :
    generationParameter G ≤ i := by
  unfold generationParameter
  split
  · exact Nat.zero_le _
  · exact csInf_le' ⟨hi, h⟩

/-- Specification of the source minimum once existence has been established. -/
theorem generationParameter_spec (heven : ¬ Odd (Nat.card G))
    (hex : ∃ i : ℕ, 0 < i ∧ IsEGenerated i G) :
    0 < generationParameter G ∧ IsEGenerated (generationParameter G) G := by
  unfold generationParameter
  rw [if_neg heven]
  exact Nat.sInf_mem hex

/-- A positive value of the parameter already ensures the minimum is attained.
This lets consumers assuming `n(G)=1` use generation without a separate
existence assumption. -/
theorem isEGenerated_generationParameter_of_pos (hpos : 0 < generationParameter G) :
    IsEGenerated (generationParameter G) G := by
  classical
  have heven : ¬ Odd (Nat.card G) := by
    intro ho
    rw [generationParameter_eq_zero_of_odd ho] at hpos
    exact Nat.lt_irrefl _ hpos
  have hex : ({i : ℕ | 0 < i ∧ IsEGenerated i G} : Set ℕ).Nonempty := by
    by_contra h
    have hempty := Set.not_nonempty_iff_eq_empty.mp h
    simp [generationParameter, heven, hempty] at hpos
  exact (generationParameter_spec heven hex).2

/-- The generation step used in F.7.13: if the weak-closure normalizer lies
in a proper subgroup, an E-member escapes that subgroup. -/
theorem IsEGeneratedAt.exists_member_not_le {i : ℕ} {T : Sylow 2 G}
    (hgen : IsEGeneratedAt i T) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M) :
    ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
      ∃ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K ∧ ¬ K ≤ M := by
  classical
  by_contra h
  have hall : ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
      ∀ K : Subgroup G, IsEMemberAt i (T : Subgroup G) A K → K ≤ M := by
    intro A hA hAT K hK
    by_contra hKM
    exact h ⟨A, hA, hAT, K, hK, hKM⟩
  have he : eFamilySubgroup i (T : Subgroup G) Ω ≤ M := by
    apply iSup_le
    intro A
    exact sSup_le fun K hK => hall A.1 A.2.1 A.2.2 K hK
  exact hM (top_unique (hgen Ω hΩ ▸ sup_le he hnorm))

/-- In particular, the hypothesis `n(G)=1` in F.7.13 supplies an actual
rank-one E-member outside the specified proper subgroup. -/
theorem exists_rankOne_member_of_parameter_eq_one (hn : generationParameter G = 1)
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (M : Subgroup G) (hM : M ≠ ⊤)
    (hnorm : normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M) :
    ∃ A : Subgroup G, A ∈ Ω ∧ A ≤ (T : Subgroup G) ∧
      ∃ K : Subgroup G, IsEMemberAt 1 (T : Subgroup G) A K ∧ ¬ K ≤ M := by
  have hgen := isEGenerated_generationParameter_of_pos (G := G) (by omega)
  rw [hn] at hgen
  exact (hgen T).exists_member_not_le Ω hΩ M hM hnorm

end CFSG.Quasithin.ChapterE
