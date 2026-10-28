module

public import CFSG.Quasithin.ChapterJ.Section01To02.SpecialCore.SingerCentralizers.Nonabelian
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# Coprime splitting and cubic transport for the Singer centralizer

For the actual order-seven choice, coprime action splits C_S(s) as the
join of S₀ and [C_S(s),B₇], once S₀ is known to be abelian. A trivial
Singer fixed subgroup in V places V in the moving factor. Cubic
transitivity on S₀ and invariance of the moving factor make these two
factors commute. The nonabelian-centralizer theorem then excludes an
abelian moving factor, and also proves the exact exponent four.

The fixed-space, transitivity and invariance inputs are left explicit for
the concrete Singer restriction calculation. No existence of the Singer
choice or full J.2.3 conclusion is asserted here. The full-commutator
premise is the independent J.2.3(6) input.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma J.2.3(1),(3)–(6), printed pp.433–434 (PDF pp.444–445).
-/

@[expose] public section
noncomputable section
open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.ChapterJ.SpecialCore
variable {G : Type*} [Group G] [Finite G]

/-- The Singer group acts on the literal element centralizer. -/
theorem SingerChoice.normalizes_coreCentralizer (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B) (s : G)
    (hs : s ∈ fixedCore d c.B7) :
    c.B7 ≤ normalizer (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) := by
  have hcs : c.B7 ≤ centralizer ({s} : Set G) := by
    intro b hb
    exact mem_centralizer_singleton_iff.mpr (hs.2 b hb)
  exact (le_inf (c.le_L.trans d.ru1.steinberg.normalized)
    (hcs.trans (centralizer ({s} : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf

/-- Coprime splitting with the literal fixed and moving factors. -/
theorem SingerChoice.coreCentralizer_eq_sup (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hab : IsMulCommutative (fixedCore d c.B7))
    (s : G) (hs : s ∈ fixedCore d c.B7) :
    d.S ⊓ centralizer ({s} : Set G) = fixedCore d c.B7 ⊔ movingCore d c.B7 s := by
  let C := d.S ⊓ centralizer ({s} : Set G)
  let _ : Group.IsNilpotent C := ((isPGroup_pCoreIn 2 d.L).to_le (show C ≤ d.S from inf_le_left)).isNilpotent
  have hcop : Nat.Coprime (Nat.card c.B7) (Nat.card C) := by
    apply Nat.Coprime.of_dvd_right (card_dvd_of_le (show C ≤ d.S from inf_le_left))
    rw [c.card_seven,d.ru1.card_S]
    decide
  have he := eq_commutator_sup_centralizer_of_solvable_coprime C c.B7
    (c.normalizes_coreCentralizer d B s hs) inferInstance hcop
  have hf : C ⊓ centralizer (c.B7 : Set G) = fixedCore d c.B7 := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) inf_le_right
    · intro x hx
      exact ⟨⟨hx.1, mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hab.is_comm.comm ⟨x,hx⟩ ⟨s,hs⟩))⟩,hx.2⟩
  rw [hf,sup_comm] at he
  exact he

/-- The common kernel belongs to the moving factor when the Singer group
has no nonidentity fixed point on V. -/
theorem SingerChoice.V_le_movingCore (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hdis : Disjoint (fixedCore d c.B7) d.V)
    (s : G) (hs : s ∈ d.S) : d.V ≤ movingCore d c.B7 s := by
  have hn : c.B7 ≤ normalizer d.V := c.le_L.trans d.ru1.normalizer_eq.le
  have hf : d.V ⊓ centralizer (c.B7 : Set G) = ⊥ := by
    apply le_bot_iff.mp
    intro v hv
    exact hdis.le_bot ⟨⟨d.ru1.steinberg.kernel_le hv.1,hv.2⟩,hv.1⟩
  let _ : Group.IsNilpotent d.V :=
    ((isPGroup_pCoreIn 2 d.L).to_le d.ru1.steinberg.kernel_le).isNilpotent
  have he := eq_commutator_sup_centralizer_of_solvable_coprime d.V c.B7 hn
    inferInstance (by rw [c.card_seven,d.ru1.card_V]; decide)
  rw [hf,sup_bot_eq] at he
  rw [he]
  exact commutator_mono (d.ru1.V_le_coreCentralizer ⟨s,hs⟩) le_rfl

/-- Actual cubic conjugation preserves the moving factor once it preserves C_S(s). -/
theorem SingerChoice.normalizes_movingCore (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B) (s : G)
    (hn : cubicSubgroup d B ≤ normalizer (d.S ⊓ centralizer ({s} : Set G) : Subgroup G)) :
    cubicSubgroup d B ≤ normalizer (movingCore d c.B7 s) := by
  intro b hb
  rw [mem_normalizer_iff_map_conj_eq]
  change (⁅d.S ⊓ centralizer ({s} : Set G),c.B7⁆).map (MulAut.conj b : G →* G) = _
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hn hb),
    mem_normalizer_iff_map_conj_eq.mp (c.normalized hb)]
  rfl

/-- Cubic transitivity on S₀ turns centralization of one nonidentity s
into centralization of the entire fixed factor. -/
theorem SingerChoice.movingCore_centralizes_fixedCore (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B) (s : G)
    (hs : s ∈ fixedCore d c.B7)
    (hn : cubicSubgroup d B ≤ normalizer (movingCore d c.B7 s))
    (htrans : ∀ x ∈ fixedCore d c.B7, x ≠ 1 →
      ∃ b ∈ cubicSubgroup d B, b * s * b⁻¹ = x) :
    movingCore d c.B7 s ≤ centralizer (fixedCore d c.B7 : Set G) := by
  have hMC : movingCore d c.B7 s ≤ d.S ⊓ centralizer ({s} : Set G) :=
    le_normalizer_iff_commutator_le_left.mp (c.normalizes_coreCentralizer d B s hs)
  intro m hm x hx
  by_cases hx1 : x = 1
  · simp [hx1]
  obtain ⟨b,hb,rfl⟩ := htrans x hx hx1
  have hm' : b⁻¹ * m * b ∈ movingCore d c.B7 s := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp (hn ((cubicSubgroup d B).inv_mem hb)) m).mp hm
  have hc := mem_centralizer_singleton_iff.mp (hMC hm').2
  have he := congrArg (MulAut.conj b) hc
  simpa [MulAut.conj_apply, mul_assoc] using he.symm

/-- Source nonabelianness of the moving factor follows from the intersection
argument; it is not a hypothesis. -/
theorem SingerChoice.movingCore_nonabelian (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G),d.S⁆ = d.V)
    (hab : IsMulCommutative (fixedCore d c.B7))
    (hdis : Disjoint (fixedCore d c.B7) d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1)
    (hn : cubicSubgroup d B ≤ normalizer (movingCore d c.B7 s))
    (htrans : ∀ x ∈ fixedCore d c.B7, x ≠ 1 →
      ∃ b ∈ cubicSubgroup d B, b * s * b⁻¹ = x) :
    ¬ IsMulCommutative (movingCore d c.B7 s) := by
  have hsv : s ∉ d.V := fun hv => hs1 (hdis.le_bot ⟨hs,hv⟩)
  intro hm
  apply d.ru1.coreCentralizer_nonabelian hfull ⟨s,hs.1⟩ hsv
  rw [c.coreCentralizer_eq_sup d B hab s hs]
  apply le_centralizer_iff_isMulCommutative.mp
  have hc := c.movingCore_centralizes_fixedCore d B s hs hn htrans
  apply sup_le
  · exact le_centralizer_iff.mpr (sup_le
      (le_centralizer_iff_isMulCommutative.mpr hab) hc)
  · exact le_centralizer_iff.mpr (sup_le (le_centralizer_iff.mp hc)
      (le_centralizer_iff_isMulCommutative.mpr hm))

/-- The numerical and exact-exponent clauses for the source's chosen s. -/
theorem SingerChoice.coreCentralizer_order_exponent (d : TypeRuSetup G)
    (B : Sylow 3 d.L₁) (c : SingerChoice d B)
    (hfull : ∀ t : d.S, (t : G) ∉ d.V → ⁅zpowers (t : G),d.S⁆ = d.V)
    (hdis : Disjoint (fixedCore d c.B7) d.V)
    (s : G) (hs : s ∈ fixedCore d c.B7) (hs1 : s ≠ 1) :
    Nat.card (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 256 ∧
    Monoid.exponent (d.S ⊓ centralizer ({s} : Set G) : Subgroup G) = 4 := by
  have hsv : s ∉ d.V := fun hv => hs1 (hdis.le_bot ⟨hs,hv⟩)
  exact ⟨d.ru1.centralizer_card_of_full_commutator ⟨s,hs.1⟩ (hfull ⟨s,hs.1⟩ hsv),
    d.ru1.coreCentralizer_exponent_eq_four hfull ⟨s,hs.1⟩ hsv⟩
end CFSG.Quasithin.ChapterJ.SpecialCore
