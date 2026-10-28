module

public import CFSG.Quasithin.ChapterJ.Section01To02.ParabolicStructure.SylowChoice.Action
public import Theory.Representation.PSL3Two.NaturalOrbits
public import Theory.GroupTheory.EmbeddedCenterMap

/-!
# The source-compatible Sylow choice for groups of type Ru

The given Ru1/Ru2 witness already has |Z(T)| = 2 and Z(T) ≤ V. Ru2 then
computes the Sylow order, showing that L contains an ambient Sylow R.
The Ru1 natural action conjugates Z(R) to the original Z(T) by an element
of L. The resulting Sylow stays in L and has exactly the original center.
Consequently H, Q, U and all Ru2 coordinate maps remain literally the same.
This proves the choice at the start of J.2 from the existing existential
IsTypeRu interface, without a universal Ru2 hypothesis or a change to Defs.

Source: Aschbacher–Smith, J.1 (Ru1–Ru2), printed p.431, and the Sylow
choice at the start of J.2, printed p.432 (manuscript of 1 March 2004).
-/

public section
noncomputable section
namespace CFSG.Quasithin.ChapterJ
open Subgroup Representation
variable {G : Type*} [Group G]

private def ruTwoFromCenter (V : Subgroup G) (T : Sylow 2 G)
    (Z : Subgroup G) (hZ : sylowCenter T = Z)
    (q : centralizer (Z : Set G) →* S5) (hs : Function.Surjective q)
    (hk : q.ker = ((centralizer (Z : Set G)).pCoreIn 2).subgroupOf
      (centralizer (Z : Set G)))
    (a : L2FourAction)
    (n : BinaryConjugationSection (centralizer (Z : Set G))
      (conjugateSpan (centralizer (Z : Set G)) V) Z (a.action.comp q))
    (b : Representation (ZMod 2) S5 SixSpace) (hb : Indecomposable b)
    (s : BinaryConjugationSection (centralizer (Z : Set G))
      ((centralizer (Z : Set G)).pCoreIn 2)
      (conjugateSpan (centralizer (Z : Set G)) V) (b.comp q)) : RuTwo V T := by
  subst Z
  exact ⟨q, hs, hk, a, n, b, hb, s⟩

/-- Ru2 transports when the actual Sylow center is unchanged. -/
def RuTwo.of_sylowCenter_eq {V : Subgroup G} {T R : Sylow 2 G}
    (r : RuTwo V T) (h : sylowCenter R = sylowCenter T) : RuTwo V R :=
  ruTwoFromCenter V R (sylowCenter T) h r.quotientMap r.quotient_surjective
    r.quotient_kernel r.naturalAction r.natural r.sixAction r.indecomposable r.six

private theorem sylowCenter_smul (T : Sylow 2 G) (g : G) :
    sylowCenter (g • T) = (sylowCenter T).map (MulAut.conj g).toMonoidHom := by
  have h : ((g • T : Sylow 2 G) : Subgroup G) =
      (T : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  unfold sylowCenter
  rw [h]
  exact (map_embeddedCenter (T : Subgroup G) (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).symm

private theorem RuOne.conjugate_nonidentity {L V : Subgroup G} (r : RuOne L V)
    (v w : V) (hv : v ≠ 1) (hw : w ≠ 1) :
    ∃ l : L, (l : G) * (v : G) * (l : G)⁻¹ = w := by
  have hi : Function.Injective r.natural.coordinates := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    rw [r.natural.kernel_eq, bot_subgroupOf]
  have hne (x : V) (hx : x ≠ 1) : (r.natural.coordinates x).toAdd ≠ 0 := by
    intro he
    exact hx (hi (he.trans r.natural.coordinates.map_one.symm))
  obtain ⟨a, ha⟩ := BinaryLinearThree.natural_transitive_nonzero
    (r.natural.coordinates v).toAdd (r.natural.coordinates w).toAdd (hne v hv) (hne w hw)
  obtain ⟨l, hl⟩ := r.quotient_surjective a
  have he := r.natural.equivariant l v
  change _ = BinaryLinearThree.W (r.quotientMap l) _ at he
  rw [hl, ha] at he
  exact ⟨l, congrArg Subtype.val (hi (Multiplicative.toAdd.injective he))⟩

variable [Finite G]

/-- Choose a Sylow inside L with the original Ru2 center, preserving V and L. -/
theorem TypeRuSetup.exists_sylow_le_L_same_center (d : TypeRuSetup G) :
    ∃ R : Sylow 2 G, (R : Subgroup G) ≤ d.L ∧ sylowCenter R = d.Z := by
  let P : Sylow 2 d.L := Sylow.nonempty.some
  obtain ⟨R, hPR⟩ := (P.isPGroup'.map d.L.subtype).exists_le_sylow
  have hPcard : Nat.card P = 16384 := by
    rw [P.card_eq_multiplicity, d.ru1.card_L]
    decide +kernel
  have hRcard : Nat.card R = 16384 :=
    (Nat.card_congr (R.equiv d.T).toEquiv).trans (d.card_T_of_card_Z d.card_Z)
  have hR : (P : Subgroup d.L).map d.L.subtype = (R : Subgroup G) := by
    apply eq_of_le_of_card_ge hPR
    rw [card_map_of_injective d.L.subtype_injective, hPcard, hRcard]
  have hRL : (R : Subgroup G) ≤ d.L := hR.symm.le.trans (map_subtype_le _)
  have hSR : d.S ≤ (R : Subgroup G) := (pCoreIn_le_sylow d.L P).trans hPR
  have hZRV : sylowCenter R ≤ d.V :=
    (d.ru1.sylowCenter_eq_of_core_le R hSR).le.trans inf_le_left
  obtain ⟨z₀, hz₀, huniq⟩ := (Nat.card_eq_two_iff' (1 : sylowCenter R)).mp
    (d.ru1.card_sylowCenter R)
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : d.Z)).mp d.card_Z
  obtain ⟨l, hl⟩ := d.ru1.conjugate_nonidentity
    ⟨z₀, hZRV z₀.property⟩ ⟨z, d.Z_le_V z.property⟩
    (fun h => hz₀ (Subtype.ext (congrArg (fun v : d.V => (v : G)) h)))
    (fun h => hz (Subtype.ext (congrArg (fun v : d.V => (v : G)) h)))
  have hconj : (sylowCenter R).map (MulAut.conj (l : G)).toMonoidHom = d.Z := by
    apply eq_of_le_of_card_ge
    · rintro x ⟨a, ha, rfl⟩
      by_cases ha1 : a = 1
      · simpa only [ha1, map_one] using d.Z.one_mem
      · have he : (⟨a, ha⟩ : sylowCenter R) = z₀ :=
          huniq _ (fun h => ha1 (congrArg Subtype.val h))
        change (l : G) * a * (l : G)⁻¹ ∈ d.Z
        rw [show a = (z₀ : G) from congrArg Subtype.val he, hl]
        exact z.property
    · rw [card_map_of_injective (MulAut.conj (l : G)).injective,
        d.ru1.card_sylowCenter R, d.card_Z]
  refine ⟨(l : G) • R, ?_, (sylowCenter_smul R l).trans hconj⟩
  change (R : Subgroup G).map (MulAut.conj (l : G)).toMonoidHom ≤ d.L
  rintro x ⟨a, ha, rfl⟩
  exact d.L.mul_mem (d.L.mul_mem l.property (hRL ha)) (d.L.inv_mem l.property)

/-- The source choice retains L, V and the original Sylow center, hence all Ru2 groups. -/
theorem TypeRuSetup.exists_localSetup (d : TypeRuSetup G) :
    ∃ c : LocalSetup G, c.L = d.L ∧ c.V = d.V ∧ sylowCenter c.T = d.Z := by
  obtain ⟨R, hRL, hRZ⟩ := d.exists_sylow_le_L_same_center
  let c : LocalSetup G := {
    L := d.L
    V := d.V
    T := R
    ru1 := d.ru1
    ru2 := d.ru2.of_sylowCenter_eq hRZ
    sylowInL := R.subtype hRL
    intersection_eq := by
      change (R : Subgroup G) ⊓ d.L =
        ((R : Subgroup G).subgroupOf d.L).map d.L.subtype
      rw [inf_eq_left.mpr hRL, map_subgroupOf_eq_of_le hRL] }
  exact ⟨c, rfl, rfl, hRZ⟩

/-- The Sylow choice at the start of J.2 follows from the existing type-Ru hypotheses. -/
theorem IsTypeRu.nonempty_localSetup (h : IsTypeRu G) : Nonempty (LocalSetup G) := by
  obtain ⟨d⟩ := h
  obtain ⟨c, _⟩ := d.exists_localSetup
  exact ⟨c⟩

end CFSG.Quasithin.ChapterJ
