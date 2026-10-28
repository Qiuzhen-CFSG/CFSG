module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Centralizer.Generation.Action
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.PairingControl.Geometry.Selection.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.Escape.EdgeTransfer.Basic
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Existence of a neighbor with the required relative centralizer

The two-group Q_t fixes a nonidentity element u of the natural eight-group
U_c. The normal core of an edge displacement is trivial by natural
irreducibility and its order bound. Consequently a conjugate displacement
plane omits u. This plane together with u generates U_c, so its centralizer
inside Q_t is exactly Q_c, the faithful natural-action kernel.

This selects an actual neighbor of c, without selecting a critical endpoint
or asserting that all the eligible neighboring radius groups generate V_c.
Only the earlier source data and the supplied initial and contrary facts
are used.

Source: Meierfrankenfeld--Stellmacher (1993), the display before (4.3.2)(4),
printed p.884.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M} {geometry : MS93.Geometry R}

/-- A nonidentity natural vector fixed by the actual incident two-group. -/
theorem exists_fixed_natural_element (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    ∃ u : FreeAmalgam R, u ∈ U R c ∧
      u ∈ centralizer (Q R t : Set (FreeAmalgam R)) ∧ u ≠ 1 := by
  let P := Q R t
  let := finite_stabilizer R t
  let : Finite P := Finite.of_injective
    (inclusion (show P ≤ stabilizer R t from fun _ hx => hx.1)) (inclusion_injective _)
  have hUP : U R c ≤ P := by
    apply (U_le_Z c).trans
    apply Z_le_Q_of_dist_lt R c (geometry.exists_critical c hc)
    rw [geometry.distance_constant c hc,
      SimpleGraph.dist_eq_one_iff_adj.mpr ((cosetGraph_adj R _ _).mpr hct)]
    exact lt_trans (by decide : 1 < 2) hb
  have hPG : P ≤ stabilizer R c := fun _ hx => hx.2 c (adjacent_symm R hct)
  let D := (U R c).subgroupOf P
  let : D.Normal := normal_subgroupOf_of_le_normalizer (hPG.trans (U_normalized c))
  have hD : D ≠ ⊥ := by
    intro h
    have hh := congrArg (Subgroup.map P.subtype) h
    rw [map_subgroupOf_eq_of_le hUP, Subgroup.map_bot] at hh
    have hcard := modules.natural.card_at c hc
    rw [hh, card_bot] at hcard
    omega
  have hne := center_inf_ne_bot_of_normal (EdgeTransfer.edge_kernel_two source c t hc hct) D hD
  obtain ⟨u, hu, hune⟩ := (center P ⊓ D).bot_or_exists_ne_one.resolve_left hne
  refine ⟨u, hu.2, ?_, ?_⟩
  · intro x hx
    exact congrArg Subtype.val ((mem_center_iff.mp hu.1) ⟨x, hx⟩)
  · intro h
    exact hune (Subtype.ext h)

private theorem avoiding_edge (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (facts : ContraryLocalFacts geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t)
    {u : FreeAmalgam R} (hu : u ∈ U R c) (hne : u ≠ 1) :
    ∃ s, Adjacent R c s ∧ u ∉ edgeDisplacement c s := by
  let S := stabilizer R c
  let D := (edgeDisplacement c t).subgroupOf S
  let N := D.normalCore
  have hUS : U R c ≤ S := (U_le_Z c).trans (Z_le_stabilizer R c)
  have hDU : edgeDisplacement c t ≤ U R c := Initial.edge_le_natural source c t hc hct
  obtain ⟨o⟩ := facts.opposite c hc
  have hπ : (⊤ : Subgroup S).map o.projection = ⊤ := by
    rw [← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr o.surjective
  have hN : N = ⊥ := by
    rcases o.naturalU.irreducible hπ N (fun _ hx => hDU (D.normalCore_le hx))
      le_normalizer_of_normal with h | h
    · exact h
    · have hUD : U R c ≤ edgeDisplacement c t := by
        intro x hx
        exact D.normalCore_le (show (⟨x, hUS hx⟩ : S) ∈ N from h.symm ▸ hx)
      have heq := le_antisymm hDU hUD
      have hsmall := Initial.edge_card_le_four source hb modules c t hc hct
      rw [heq, modules.natural.card_at c hc] at hsmall
      omega
  have hex : ∃ g : S, (g : FreeAmalgam R) * u * (g : FreeAmalgam R)⁻¹ ∉ edgeDisplacement c t := by
    by_contra! h
    have hmem : (⟨u, hUS hu⟩ : S) ∈ N := h
    rw [hN, mem_bot] at hmem
    exact hne (congrArg Subtype.val hmem)
  obtain ⟨g, hg⟩ := hex
  refine ⟨act R g t, ?_, ?_⟩
  · have ha := (adjacent_act_iff R g c t).mpr hct
    simpa only [show act R (g : FreeAmalgam R) c = c from g.property] using ha
  · intro hm
    have he := FirstPairing.edgeDisplacement_act (g : FreeAmalgam R) c t
    rw [show act R (g : FreeAmalgam R) c = c from g.property] at he
    rw [he] at hm
    obtain ⟨v, hv, hvu⟩ := hm
    apply hg
    have heq : (g : FreeAmalgam R) * u * (g : FreeAmalgam R)⁻¹ = v := by
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe,
        MulAut.conj_apply, inv_inv] at hvu
      rw [← hvu]
      group
    exact heq.symm ▸ hv

private theorem four_sup_outside_eq_eight {G : Type*} [Group G]
    (U D : Subgroup G) [Finite U] (hDU : D ≤ U)
    (hU : Nat.card U = 8) (hD : Nat.card D = 4)
    {u : G} (hu : u ∈ U) (hout : u ∉ D) : D ⊔ zpowers u = U := by
  let K := D ⊔ zpowers u
  have hKU : K ≤ U := sup_le hDU (zpowers_le.mpr hu)
  let : Finite K := Finite.of_injective (inclusion hKU) (inclusion_injective _)
  have hlt : 4 < Nat.card K := by
    by_contra! h
    have heq : D = K := eq_of_le_of_card_ge le_sup_left (h.trans hD.ge)
    exact hout (heq.symm ▸ (show u ∈ K from mem_sup_right (mem_zpowers u)))
  have hdvd := card_dvd_of_le hKU
  rw [hU] at hdvd
  have hdiv := Nat.mem_divisors.mpr ⟨hdvd, (by decide : 8 ≠ 0)⟩
  rw [show Nat.divisors 8 = ({1, 2, 4, 8} : Finset ℕ) by decide] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  apply eq_of_le_of_card_ge hKU
  rw [hU]
  omega

/-- A displacement plane omitting a fixed nonidentity natural vector has
exactly Q_c as its relative centralizer in the incident two-group. -/
theorem centralizer_eq_of_fixed_outside (source : LocalSource L R)
    (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (p : Counterexample geometry) (hb : 0 < geometry.b R)
    {c t s : Vertex R} (hc : color R c = false)
    (hct : Adjacent R c t) (hcs : Adjacent R c s)
    {u : FreeAmalgam R} (hu : u ∈ U R c)
    (hfix : u ∈ centralizer (Q R t : Set (FreeAmalgam R)))
    (hs : u ∉ edgeDisplacement c s) :
    Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c := by
  have hD := Initial.edge_le_natural source c s hc hcs
  have hcD := FirstPairing.StepThree.edge_card p hb initial c s hc hcs
  let : Finite (U R c) := Nat.finite_of_card_ne_zero (by rw [modules.natural.card_at c hc]; decide)
  have hgen := four_sup_outside_eq_eight (U R c) (edgeDisplacement c s) hD
    (modules.natural.card_at c hc) hcD hu hs
  apply le_antisymm
  · rintro x ⟨hx, hxc⟩
    rw [← modules.natural.centralizer c hc]
    refine ⟨hx.2 c (adjacent_symm R hct), ?_⟩
    have hUC : U R c ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
      rw [← hgen]
      apply sup_le
      · intro d hd y hy
        have hyx : y = x := hy
        subst y
        exact (hxc d hd).symm
      · apply zpowers_le.mpr
        intro y hy
        have hyx : y = x := hy
        subst y
        exact hfix x hx
    intro v hv
    exact (hUC hv x (Set.mem_singleton x)).symm
  · intro x hx
    have ht : color R t = true := by
      have hn := adjacent_color_ne R hct
      cases ht : color R t <;> simp_all
    exact ⟨Q_le_adjacent_h R ht hct hx,
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes c hc)) |>
        le_centralizer_iff.mp |>.trans (centralizer_le (hD.trans (U_le_Z c)))) hx⟩


/-- At least one actual neighbor satisfies the source's relative centralizer
condition, without choosing any new critical endpoint. -/
theorem exists_centralizing_neighbor (source : LocalSource L R)
    (hb : 2 < geometry.b R) (modules : ModuleFacts source geometry)
    (initial : ∀ q : Counterexample geometry, Nonempty (InitialFacts q))
    (facts : ContraryLocalFacts geometry) (p : Counterexample geometry)
    {c t : Vertex R} (hc : color R c = false) (hct : Adjacent R c t) :
    ∃ s, Adjacent R c s ∧
      Q R t ⊓ centralizer (edgeDisplacement c s : Set (FreeAmalgam R)) = Q R c := by
  obtain ⟨u, hu, hfix, hne⟩ := exists_fixed_natural_element source hb modules hc hct
  obtain ⟨s, hcs, hs⟩ := avoiding_edge source hb modules facts hc hct hu hne
  exact ⟨s, hcs, centralizer_eq_of_fixed_outside source modules initial p (by omega)
    hc hct hcs hu hfix hs⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.Escape.PairingControl.Geometry.Selection.Centralizer.Generation
