module

public import Stellmacher.SectionNine.NineNineSupportData
public import Stellmacher.SectionNine.NineEightNeighborhood

/-!
# Independent terminal inputs for Stellmacher (9.9)

The maximal-subgroup identification and equation (2) force the predecessor's
support commutator to escape the first-step center. Criticality also prevents
that predecessor module from lying in the terminal core. The abelian
two-step neighborhood makes the modules at offsets b and b-2 commute, and
the neighborhood distance estimate puts the predecessor module in G at b-2.

The final helper transports the actual local normalizer of a join with Z
under an actor centralizing its fixed subgroup. It does not construct the
actor or establish a quotient model, Sylow property, or index.

These are inputs to the argument on printed pp.56–57 / PDF46–47 of
`refs/files/stellmacher-n-group.pdf`. The equation-(3) model and the terminal
normalizer/index theorem remain separate mathematical obligations.
-/

namespace Stellmacher.SectionNine

open Later SectionsFiveToSeven CosetGraphContext SevenSix

universe u

public theorem nine_nine_previous_support_not_bounded
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (data : NineNineSupportData ctx hb) :
    ¬ ⁅VAt ctx.Γ data.previous, data.support⁆ ≤
      ZAt ctx.Γ ctx.criticalPath.firstStep := by
  intro hcomm
  have hle := (le_nineNineCommutatorBound_iff _ _ _ _
    (nine_nine_previous_normalizes_first_center ctx hb data.previous
      data.previous_neighbor)).mpr ⟨le_rfl, hcomm⟩
  rw [data.maximal_eq] at hle
  have hcard := Subgroup.card_le_of_le hle
  have hpositive := Nat.card_pos (α := VAt ctx.Γ data.previous)
  have hlarge := data.large_index
  omega

public theorem nine_nine_previous_not_le_terminal_core
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (data : NineNineSupportData ctx hb) :
    ¬ VAt ctx.Γ data.previous ≤ QAt ctx.Γ ctx.criticalPath.a' := by
  have hcenter : ZAt ctx.Γ ctx.criticalPath.a ≤ VAt ctx.Γ data.previous := by
    rw [VAt, v, ctx.Γ.vAt_def]
    refine le_sSup ⟨ctx.criticalPath.a, ?_, rfl⟩
    exact (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm
        ((mem_neighborhood_iff_adjacent ctx.Γ).mp data.previous_neighbor))
  exact fun hle => ctx.criticalPath.critical.2 (hcenter.trans hle)

public theorem nine_nine_terminal_modules_commute
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length) :
    ⁅VAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩),
      VAt ctx.Γ ctx.criticalPath.a'⁆ = ⊥ := by
  have hodd := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).odd_distance
  have hlong : 4 < ctx.criticalPath.length := by
    obtain ⟨offset, hoffset⟩ := hodd
    omega
  let penultimate := ctx.criticalPath.path
    ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩
  have hleft : ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ ∈
      neighborhood ctx.Γ penultimate := by
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    have hadj := ctx.criticalPath.path_adj ⟨ctx.criticalPath.length - 2, by omega⟩
    have hnext : (⟨ctx.criticalPath.length - 2, by omega⟩ :
        Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length - 1, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hnext] at hadj
    exact ctx.Γ.adjacent_symm hadj
  have hright : ctx.criticalPath.a' ∈ neighborhood ctx.Γ penultimate := by
    apply (mem_neighborhood_iff_adjacent ctx.Γ).mpr
    have hadj := ctx.criticalPath.path_adj ⟨ctx.criticalPath.length - 1, by omega⟩
    have hend : (⟨ctx.criticalPath.length - 1, by omega⟩ :
        Fin ctx.criticalPath.length).succ =
        ⟨ctx.criticalPath.length, Nat.lt_succ_self _⟩ := by
      apply Fin.ext
      simp
      omega
    rw [hend, ctx.criticalPath.path_end] at hadj
    exact hadj
  have habelian := nine_eight_neighborhood_abelian ctx hlong penultimate
  have hcentral := (Subgroup.le_centralizer_iff_isMulCommutative).mpr habelian
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    ((nine_eight_v_le_generated_neighborhood ctx.Γ hleft).trans
      (hcentral.trans (Subgroup.centralizer_le
        (nine_eight_v_le_generated_neighborhood ctx.Γ hright))))

public theorem nine_nine_preterminal_module_centralizes_support
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (data : NineNineSupportData ctx hb) :
    ⁅VAt ctx.Γ (ctx.criticalPath.path
        ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩),
      data.support⁆ = ⊥ := by
  apply le_bot_iff.mp
  exact (Subgroup.commutator_mono le_rfl data.support_le).trans_eq
    (nine_nine_terminal_modules_commute ctx hb)

public theorem nine_nine_previous_le_preterminal_stabilizer
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B)
    (hb : 3 < ctx.criticalPath.length)
    (data : NineNineSupportData ctx hb) :
    VAt ctx.Γ data.previous ≤ GAt ctx.Γ (ctx.criticalPath.path
      ⟨ctx.criticalPath.length - 2, Nat.lt_succ_of_le (Nat.sub_le _ _)⟩) := by
  have hodd := (lemma_seven_five ctx.sectionSeven ctx.Γ ctx.criticalPath
    ctx.commutator_eq).odd_distance
  have hlong : 4 < ctx.criticalPath.length := by
    obtain ⟨offset, hoffset⟩ := hodd
    omega
  have hinitial : ctx.criticalPath.a ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep :=
    (mem_neighborhood_iff_adjacent ctx.Γ).mpr
      (ctx.Γ.adjacent_symm ctx.criticalPath.firstStep_adj)
  exact (nine_eight_v_le_generated_neighborhood ctx.Γ data.previous_neighbor).trans
    (nine_eight_neighborhood_le_preterminal ctx hlong ctx.criticalPath.a hinitial)

public theorem nine_nine_normalizer_conjugation
    {G : Type u} [Group G] [Finite G] {T A B : Subgroup G}
    (Γ : CosetGraphContext G T A B)
    (vertex : Γ.Vertex) (fixed : Subgroup G) (actor : G)
    (hactor : actor ∈ Subgroup.centralizer (fixed : Set G)) :
    (GAt Γ vertex ⊓ Subgroup.normalizer
      (fixed ⊔ ZAt Γ vertex : Subgroup G)).map (MulAut.conj actor⁻¹).toMonoidHom =
    GAt Γ (Γ.act actor vertex) ⊓ Subgroup.normalizer
      (fixed ⊔ ZAt Γ (Γ.act actor vertex) : Subgroup G) := by
  have hfixed : fixed.map (MulAut.conj actor⁻¹).toMonoidHom = fixed :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (Subgroup.centralizer_le_normalizer (fixed : Set G)
        ((Subgroup.centralizer (fixed : Set G)).inv_mem hactor))
  change ((stabilizer Γ vertex) ⊓ Subgroup.normalizer (fixed ⊔ z Γ vertex : Subgroup G)).map _ =
    stabilizer Γ (Γ.act actor vertex) ⊓ Subgroup.normalizer
      (fixed ⊔ z Γ (Γ.act actor vertex) : Subgroup G)
  rw [Subgroup.map_inf _ _ _ (MulAut.conj actor⁻¹).injective,
    Subgroup.map_equiv_normalizer_eq, Subgroup.map_sup, hfixed,
    stabilizer_act, z_act]
  rfl

end Stellmacher.SectionNine
