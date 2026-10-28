module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.LinearAction.Geometry
public import CFSG.Quasithin.ChapterE.Section03.Parameters.Global

/-!
# The ambient action of a binary PSL₂ Borel

An ambient subgroup V fixing the marked Sylow pointwise induces inner
component automorphisms with conjugators in that Sylow. Its displacement
under the Borel lies in the Sylow and is Borel-invariant. Nontriviality of
the component action and torus irreducibility make the displacement equal
to the whole Sylow, so that Sylow lies in V whenever the Borel normalizes V.
The Borel detects the whole component action kernel. Conversely, the kernel
of its action on V is exactly its Sylow subgroup; the actual induced image
is therefore isomorphic to the embedded diagonal torus.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247–248, referring to the argument of E.6.7 on printed p.246.
LinearAction.lean derives the local action hypotheses and retains Borel
placement as an explicit input.
-/

public section

set_option backward.isDefEq.respectTransparency false

open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.LinearAction
variable {G : Type*} [Group G] [Finite G] {V L B : Subgroup G}
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem inner_conjugator (e : L ≃* BenderSuzuki.Converse.PSL2 F)
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (v : G) (hv : v ∈ V) :
    ∃ s ∈ S, ∀ l : L, v * (l : G) * v⁻¹ = (s : G) * (l : G) * (s : G)⁻¹ := by
  obtain ⟨s, hs, he⟩ := fixing_sylow_inner e S
    (L.normalizerMonoidHom ⟨v, hN hv⟩) (by
      intro s hs
      exact Subtype.ext (hfix v hv ⟨s, hs⟩))
  refine ⟨s, hs, ?_⟩
  intro l
  exact congrArg Subtype.val (congrArg (fun a : MulAut L => a l) he)

omit [Finite G] in
private theorem commutator_inner (v : G) (s : L)
    (ha : ∀ l : L, v * (l : G) * v⁻¹ = (s : G) * (l : G) * (s : G)⁻¹)
    (b : L) : ⁅v, (b : G)⁆ = (⁅s, b⁆ : L) := by
  simp only [commutatorElement_def]
  rw [ha b]
  rfl

private theorem displacement_eq (e : L ≃* BenderSuzuki.Converse.PSL2 F)
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hg : SylowGeometry S (Nat.card F))
    (hB : B = (normalizer (S : Set L)).map L.subtype)
    (hne : ¬ V ≤ centralizer (L : Set G)) :
    ⁅V, B⁆ = (S : Subgroup L).map L.subtype := by
  have hmove := hg.moving
  have hirr := hg.irreducible
  have hle : ⁅V, B⁆ ≤ (S : Subgroup L).map L.subtype := by
    apply commutator_le.mpr
    intro v hv b hb
    obtain ⟨s, hs, ha⟩ := inner_conjugator e hN S hfix v hv
    obtain ⟨b, hbN, rfl⟩ := hB ▸ hb
    change ⁅v, (b : G)⁆ ∈ (S : Subgroup L).map L.subtype
    rw [commutator_inner v s ha b]
    refine mem_map.mpr ⟨⁅s, b⁆, ?_, rfl⟩
    change s * b * s⁻¹ * b⁻¹ ∈ (S : Subgroup L)
    simpa only [mul_assoc] using
      (S : Subgroup L).mul_mem hs ((hbN s⁻¹).mp ((S : Subgroup L).inv_mem hs))
  have hWL : ⁅V, B⁆ ≤ L := hle.trans (map_subtype_le _)
  have hWne : ⁅V, B⁆ ≠ ⊥ := by
    intro hbot
    apply hne
    intro v hv
    obtain ⟨s, hs, ha⟩ := inner_conjugator e hN S hfix v hv
    have hs1 : s = 1 := by
      by_contra hs1
      obtain ⟨b, hb, hm⟩ := hmove s hs hs1
      have hmem := commutator_mem_commutator hv (hB.symm ▸ mem_map_of_mem L.subtype hb)
      rw [hbot, mem_bot] at hmem
      change ⁅v, (b : G)⁆ = 1 at hmem
      rw [commutator_inner v s ha b] at hmem
      exact hm (Subtype.ext hmem)
    apply mem_centralizer_iff.mpr
    intro l hl
    have he := ha ⟨l, hl⟩
    simp only [hs1, OneMemClass.coe_one, one_mul, inv_one, mul_one] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hD : ⁅V, B⁆.subgroupOf L = S := by
    apply hirr
    · intro x hx
      obtain ⟨s, hs, he⟩ := hle hx
      exact (Subtype.ext he : s = x) ▸ hs
    · intro b hb x
      exact (normalizer_commutator_ge_right V B (hB.symm ▸ mem_map_of_mem L.subtype hb)) (x : G)
    · intro hd
      apply hWne
      have he := congrArg (Subgroup.map L.subtype) hd
      simpa only [map_subgroupOf_eq_of_le hWL, Subgroup.map_bot] using he
  have he := congrArg (Subgroup.map L.subtype) hD
  simpa only [map_subgroupOf_eq_of_le hWL] using he

omit [Finite G] [Field F] [Finite F] [CharP F 2] in
private theorem borel_centralizer
    (S : Sylow 2 L) (hg : SylowGeometry S (Nat.card F))
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hPV : (S : Subgroup L).map L.subtype ≤ V)
    (hB : B = (normalizer (S : Set L)).map L.subtype) :
    B ⊓ centralizer (V : Set G) = (S : Subgroup L).map L.subtype := by
  have hcs := hg.centralizer
  apply le_antisymm
  · rintro x ⟨hxB, hxC⟩
    obtain ⟨b, hb, rfl⟩ := hB ▸ hxB
    apply mem_map_of_mem
    apply hcs
    apply mem_centralizer_iff.mpr
    intro s hs
    exact Subtype.ext (mem_centralizer_iff.mp hxC s (hPV (mem_map_of_mem L.subtype hs)))
  · rintro x ⟨s, hs, rfl⟩
    refine ⟨hB.symm ▸ mem_map_of_mem L.subtype ((S : Subgroup L).le_normalizer hs), ?_⟩
    apply mem_centralizer_iff.mpr
    intro v hv
    exact mul_inv_eq_iff_eq_mul.mp (hfix v hv ⟨s, hs⟩)

private theorem fixed_eq (e : L ≃* BenderSuzuki.Converse.PSL2 F)
    (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hg : SylowGeometry S (Nat.card F))
    (hB : B = (normalizer (S : Set L)).map L.subtype) :
    V ⊓ centralizer (B : Set G) = V ⊓ centralizer (L : Set G) := by
  apply le_antisymm
  · rintro v ⟨hv, hc⟩
    obtain ⟨s, hs, ha⟩ := inner_conjugator e hN S hfix v hv
    have hs1 : s = 1 := by
      by_contra hs1
      obtain ⟨b, hb, hm⟩ := hg.moving s hs hs1
      have he : ⁅v, (b : G)⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
        (mem_centralizer_iff.mp hc b (hB.symm ▸ mem_map_of_mem L.subtype hb)).symm
      rw [commutator_inner v s ha b] at he
      exact hm (Subtype.ext he)
    refine ⟨hv, mem_centralizer_iff.mpr ?_⟩
    intro l hl
    have he := ha ⟨l, hl⟩
    simp only [hs1, OneMemClass.coe_one, one_mul, inv_one, mul_one] at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · exact inf_le_inf_left V (Subgroup.centralizer_le (hB ▸ map_subtype_le _))

omit [Finite G] in
private theorem image_equiv_complement {P D : Subgroup G}
    (hPN : P ≤ normalizer (V : Set G)) (hDN : D ≤ normalizer (V : Set G))
    (hPC : P ≤ centralizer (V : Set G))
    (hDC : D ⊓ centralizer (V : Set G) = ⊥) (hgen : P ⊔ D = B) :
    Nonempty (inducedAutomizer V B ≃* D) := by
  let a := V.normalizerMonoidHom.rangeRestrict
  have hkill : (P.subgroupOf (normalizer (V : Set G))).map a = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, MonoidHom.ker_rangeRestrict, normalizerMonoidHom_ker]
    exact comap_mono hPC
  have himage : inducedAutomizer V B = inducedAutomizer V D := by
    unfold inducedAutomizer
    rw [← hgen, subgroupOf_sup hPN hDN, Subgroup.map_sup, hkill, bot_sup_eq]
  let f := a.subgroupMap (D.subgroupOf (normalizer (V : Set G)))
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_bot_iff.mp
    intro x hx
    have he : V.normalizerMonoidHom x.val = 1 :=
      congrArg Subtype.val (congrArg Subtype.val hx)
    have hc : (x.val : G) ∈ centralizer (V : Set G) := by
      have hh : x.val ∈ V.normalizerMonoidHom.ker := he
      rwa [normalizerMonoidHom_ker] at hh
    have hx1 : (x.val : G) = 1 := mem_bot.mp (hDC ▸ ⟨x.property, hc⟩)
    exact mem_bot.mpr (Subtype.ext (Subtype.ext hx1))
  let e := MulEquiv.ofBijective f ⟨hinj, a.subgroupMap_surjective _⟩
  exact ⟨(MulEquiv.subgroupCongr himage).trans
    (e.symm.trans (subgroupOfEquivOfLe hDN))⟩

/-- The intrinsic action calculation for an actual finite binary PSL₂ model.
The normalizer's placement in the ambient local subgroup is not needed here. -/
theorem intrinsic_action (e : L ≃* BenderSuzuki.Converse.PSL2 F)
    (hq : 4 ≤ Nat.card F) (hN : V ≤ normalizer (L : Set G)) (S : Sylow 2 L)
    (hfix : ∀ v ∈ V, ∀ x : S, v * ((x : L) : G) * v⁻¹ = ((x : L) : G))
    (hB : B = (normalizer (S : Set L)).map L.subtype)
    (hBN : B ≤ normalizer (V : Set G)) (hne : ¬ V ≤ centralizer (L : Set G)) :
    V ⊓ centralizer (B : Set G) = V ⊓ centralizer (L : Set G) ∧
    Nat.card (⁅V, B⁆ : Subgroup G) = Nat.card F ∧
    Nonempty (inducedAutomizer V B ≃* Multiplicative (ZMod (Nat.card F - 1))) := by
  have hg := sylow_geometry e hq S
  have hW := displacement_eq e hN S hfix hg hB hne
  have hPV : (S : Subgroup L).map L.subtype ≤ V :=
    hW ▸ le_normalizer_iff_commutator_le_left.mp hBN
  have hC := borel_centralizer S hg hfix hPV hB
  refine ⟨fixed_eq e hN S hfix hg hB, ?_, ?_⟩
  · rw [hW, card_map_of_injective L.subtype_injective]
    exact hg.card
  · obtain ⟨D, hcyc, hcard, hdis, hgen⟩ := hg.complement
    let X := D.map L.subtype
    let P := (S : Subgroup L).map L.subtype
    have hPX : P ⊔ X = B := by
      change (S : Subgroup L).map L.subtype ⊔ D.map L.subtype = _
      rw [← Subgroup.map_sup, hgen, ← hB]
    have hPC : P ≤ centralizer (V : Set G) := by
      intro s hs
      obtain ⟨s, hs, rfl⟩ := hs
      apply mem_centralizer_iff.mpr
      intro v hv
      exact mul_inv_eq_iff_eq_mul.mp (hfix v hv ⟨s, hs⟩)
    have hXB : X ≤ B := hPX ▸ le_sup_right
    have hDC : X ⊓ centralizer (V : Set G) = ⊥ := by
      apply le_bot_iff.mp
      rintro x ⟨hx, hc⟩
      have hp : x ∈ P := by
        change x ∈ (S : Subgroup L).map L.subtype
        rw [← hC]
        exact ⟨hXB hx, hc⟩
      exact (disjoint_iff.mp (Subgroup.disjoint_map L.subtype_injective hdis)) ▸ ⟨hp, hx⟩
    obtain ⟨ef⟩ := image_equiv_complement (hPC.trans (Subgroup.centralizer_le_normalizer _))
      (hXB.trans hBN) hPC hDC hPX
    let _ := hcyc
    let ed := Subgroup.equivMapOfInjective D L.subtype L.subtype_injective
    let _ : IsCyclic X := isCyclic_of_surjective ed ed.surjective
    have hcX : Nat.card X = Nat.card F - 1 := by
      rw [card_map_of_injective L.subtype_injective]
      exact hcard
    exact ⟨ef.trans (mulEquivOfCyclicCardEq (by
      change Nat.card X = Nat.card (ZMod (Nat.card F - 1))
      rw [Nat.card_zmod]
      exact hcX))⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne.LinearAction
