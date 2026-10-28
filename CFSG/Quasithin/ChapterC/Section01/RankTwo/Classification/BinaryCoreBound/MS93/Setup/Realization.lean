module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.CharacteristicReduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics

/-!
# Source realization on the characteristic replacement

The native replacement has group J₀ = L T₀. Normality of L gives the literal
product decomposition, and the two-perfect component with its two-group
supplement is O²(J₀). Transporting characteristic subgroups through the
specified replacement equivalence turns minimum order into source 4.0.
The parabolic realization then supplies every field of `LocalSource` while
retaining the original matrix quotient and its restriction on L.

Source: Meierfrankenfeld--Stellmacher (1993), hypotheses on pp.827--828,
characteristic minimality on p.881 and the replacement on pp.932--933.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
namespace CharacteristicReduction
variable (d : CharacteristicReduction L R) (h : Input κ L R)

include h

omit [Finite J] in
/-- The replacement edge group is a two-group. -/
theorem radical_two_group : IsPGroup 2 d.radical :=
  ((h.radical.isPGroup.to_subgroup d.subgroup).map R.subtype).comap_subtype

/-- Source (B) is a literal product in J₀. -/
theorem reduced_product : ∀ m : d.overgroup,
    ∃ l ∈ L.subgroupOf d.overgroup, ∃ r ∈ d.radical, l * r = m := by
  let := h.component_normal
  intro m
  obtain ⟨l, hl, r, hr, he⟩ := mem_sup_of_normal_left.mp m.property
  refine ⟨⟨l, (show L ≤ d.overgroup from le_sup_left) hl⟩, hl, ⟨r, (show d.ambient ≤ d.overgroup from le_sup_right) hr⟩, hr, ?_⟩
  exact Subtype.ext he

/-- The transported original component is exactly O²(J₀). -/
theorem reduced_residual : pResidual 2 d.overgroup = L.subgroupOf d.overgroup := by
  let := h.component_normal
  have hp : IsPPerfect 2 L := by
    rw [← h.residual_eq]
    exact isPPerfect_pResidual 2
  have hp' := hp.of_surjective
    (subgroupOfEquivOfLe (show L ≤ d.overgroup from le_sup_left)).symm.toMonoidHom
    (subgroupOfEquivOfLe (show L ≤ d.overgroup from le_sup_left)).symm.surjective
  exact pResidual_eq_of_isPPerfect_sup _ _ hp' (d.radical_two_group h)
    (codisjoint_subgroupOf_sup L d.ambient).eq_top

omit [Group J] [Finite J] h in
private theorem characteristic_comap_equiv'
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (C : Subgroup B) [C.Characteristic] : (C.comap e.toMonoidHom).Characteristic := by
  apply characteristic_iff_le_comap.mpr
  intro a x hx
  change e (a x) ∈ C
  have hh := characteristic_iff_le_comap.mp (inferInstance : C.Characteristic)
    ((e.symm.trans a).trans e) hx
  change e (a (e.symm (e x))) ∈ C at hh
  simpa only [MulEquiv.symm_apply_apply] using hh

/-- Source 4.0 follows from the native minimum-order choice. -/
theorem reduced_minimal : CharacteristicMinimal (L.subgroupOf d.overgroup) d.radical := by
  intro C hC hcut
  let := hC
  let := d.characteristic
  let e := d.radicalEquiv
  let K : Subgroup d.subgroup := C.comap e.toMonoidHom
  let : K.Characteristic := characteristic_comap_equiv' e C
  let A : Subgroup R := K.map d.subgroup.subtype
  let : A.Characteristic := inferInstance
  have hKC : K.map e.toMonoidHom = C := by
    dsimp only [K]
    rw [map_comap_eq, MonoidHom.range_eq_top_of_surjective e.toMonoidHom e.surjective,
      top_inf_eq]
  have he : A.map R.subtype = (C.map d.radical.subtype).map d.overgroup.subtype := by
    rw [← hKC, map_map, map_map, map_map]
    rfl
  have hjoin : ((L.subgroupOf d.overgroup) ⊔ C.map d.radical.subtype).map
      d.overgroup.subtype = L ⊔ A.map R.subtype := by
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (show L ≤ d.overgroup from le_sup_left), he]
  have hAc : (L ⊔ A.map R.subtype) ⊓ pCore 2 J ≤ A.map R.subtype := by
    rintro x ⟨hx, hn⟩
    rw [← hjoin] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [he]
    apply mem_map_of_mem
    apply hcut
    exact ⟨hy, (d.core_eq h).symm ▸ hn⟩
  have hA : A = d.subgroup := eq_of_le_of_card_ge (map_subtype_le K)
    (d.card_minimal A inferInstance hAc)
  have hK : K = ⊤ := by
    apply map_injective d.subgroup.subtype_injective
    simpa only [← MonoidHom.range_eq_map, range_subtype] using hA
  rw [← hKC, hK, map_top_of_surjective _ e.surjective]


/-- The complete source local data from the actual characteristic replacement. -/
noncomputable def localSource : LocalSource (L.subgroupOf d.overgroup) d.radical := by
  classical
  let w := exists_binary_parabolic_realization d.radical (d.radical_two_group h)
    (d.projection h) (d.projection_surjective h) (d.projection_kernel h)
  let g := Classical.choose w
  have hw := Classical.choose_spec (Classical.choose_spec w)
  exact {
    two_group := d.radical_two_group h
    core_le := d.core_le_radical h
    characteristic := d.msCharacteristic h
    product := d.reduced_product h
    residual := d.reduced_residual h
    minimal := d.reduced_minimal h
    projection := d.projection h
    projection_surjective := d.projection_surjective h
    projection_kernel := d.projection_kernel h
    flag := g
    edge_in_borel := hw.1
    weakBN := hw.2.2.1
    rank_one_generation := hw.2.2.2.trans (d.reduced_residual h) }

/-- The source uses precisely the restricted original quotient map. -/
theorem localSource_projection : (d.localSource h).projection = d.projection h := rfl

/-- On the component this is the specified quotient isomorphism. -/
theorem localSource_projection_component (l : L) :
    (d.localSource h).projection ⟨l, (show L ≤ d.overgroup from le_sup_left) l.property⟩ =
      h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) :=
  h.coreProjection_component l

/-- A nontrivial preserved core forces a nontrivial edge group. -/
theorem radical_ne_bot (hD : commutatorCore L ≠ ⊥) : d.radical ≠ ⊥ := by
  intro hr
  have hc : pCore 2 d.overgroup = ⊥ := le_bot_iff.mp (hr ▸ d.core_le_radical h)
  apply hD
  rw [← d.commutatorCore_eq h, hc, commutator_bot_left, Subgroup.map_bot]

end CharacteristicReduction
end CFSG.Quasithin.ChapterC.BinaryMS.MS93

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M]

omit [Finite M] in
/-- For source E = O₂(M), its own two-core is all of E. -/
theorem twoCore_idempotent : pCore 2 (pCore 2 M) = ⊤ := by
  apply top_unique
  exact le_sSup ⟨inferInstance, pCore_isPGroup.to_subgroup ⊤⟩

/-- All three source (A) clauses for E = O₂(M), including the literal
product supplement condition. No source classification conclusion is used. -/
theorem twoCore_source_A (L : Subgroup M) :
    pPrimeCore 2 (pCore 2 M) = ⊥ ∧
    Nat.Coprime 2 (Nat.card ((pCore 2 M) ⧸ pCore 2 (pCore 2 M))) ∧
    ∀ F : Subgroup M, L ≤ pCore 2 M ⊔ F →
      ∀ e : pCore 2 M, ∃ f ∈ F, ∃ q ∈ (pCore 2 (pCore 2 M)).map (pCore 2 M).subtype,
        f * q = (e : M) := by
  refine ⟨?_, ?_, ?_⟩
  · have hp : IsPGroup 2 (pPrimeCore 2 (pCore 2 M)) := pCore_isPGroup.to_subgroup _
    rcases hp.card_eq_or_dvd with hc | hc
    · exact card_eq_one.mp hc
    · exact ((Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)).mp
        (pPrimeCore_coprime_card (p := 2) (G := pCore 2 M)) hc).elim
  · rw [twoCore_idempotent]
    simp
  · intro F _ e
    refine ⟨1, one_mem F, e, ?_, one_mul _⟩
    rw [twoCore_idempotent]
    exact mem_map_of_mem _ (mem_top e)


namespace LocalSource
variable {L R : Subgroup M} (s : LocalSource L R)

/-- The actual Sylow containing the edge subgroup at the selected flag. -/
noncomputable def borelSylow : Sylow 2 M :=
  liftedBorelSylow s.projection s.projection_surjective
    (by rw [s.projection_kernel]; exact pCore_isPGroup) s.flag

omit [Finite M] in
/-- This Sylow is exactly the inverse image of the actual flag Borel. -/
theorem borelSylow_eq : (s.borelSylow : Subgroup M) =
    (modelBorel s.flag).comap s.projection :=
  coe_liftedBorelSylow s.projection s.projection_surjective
    (by rw [s.projection_kernel]; exact pCore_isPGroup) s.flag

omit [Finite M] in
/-- Source (P)'s Sylow containment, with the same quotient marking. -/
theorem le_borelSylow : R ≤ (s.borelSylow : Subgroup M) := by
  rw [s.borelSylow_eq]
  exact s.edge_in_borel

end LocalSource

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
