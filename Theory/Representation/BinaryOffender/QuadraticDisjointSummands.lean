module

public import Theory.Representation.BinaryOffender.SubspaceAction

/-!
# Quadratic actors on a pair of disjoint summands

Suppose an actor element a carries I to a disjoint summand. Quadraticity
forces each displacement on I to be fixed by a. If another actor element b
preserves I, its displacements lie both in I and in aI, and therefore vanish.
If b commutes with a and the two summands span the module, b fixes everything.

This excludes nontrivial stabilizers of paired constituents in faithful
quadratic representations, as needed for the natural-plus-dual alternative
in Aschbacher–Smith 13.8.25, printed pp.959–960 (1 March 2004 manuscript).
No irreducibility or dimension hypothesis is needed for this linear step.
-/

public section

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A stabilizing element of a quadratic actor fixes a summand moved disjointly
by another element of the actor. -/
theorem quadratic_fixes_disjoint_summand (I : Submodule (ZMod 2) V)
    {A : Subgroup G} (hq : IsQuadratic ρ A) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (hdis : Disjoint I (I.map (ρ a)))
    (hstable : ∀ v ∈ I, ρ b v ∈ I) : ∀ v ∈ I, ρ b v = v := by
  intro v hv
  have hd : ρ b v - v ∈ I := I.sub_mem (hstable v hv) hv
  have hda : ρ b v - v ∈ I.map (ρ a) := ⟨ρ b v - v, hd, hq a ha b hb v⟩
  exact sub_eq_zero.mp (Submodule.disjoint_def.mp hdis _ hd hda)

/-- For a faithful representation spanned by the exchanged pair, a commuting
element stabilizing one summand is the identity. -/
theorem quadratic_pair_stabilizer_eq_one (hfaith : Function.Injective ρ)
    (I : Submodule (ZMod 2) V) {A : Subgroup G} (hq : IsQuadratic ρ A)
    {a b : G} (ha : a ∈ A) (hb : b ∈ A) (hab : Commute b a)
    (hdis : Disjoint I (I.map (ρ a))) (hspan : I ⊔ I.map (ρ a) = ⊤)
    (hstable : ∀ v ∈ I, ρ b v ∈ I) : b = 1 := by
  have hfix := quadratic_fixes_disjoint_summand ρ I hq ha hb hdis hstable
  apply hfaith
  ext v
  have hv : v ∈ I ⊔ I.map (ρ a) := hspan.symm ▸ Submodule.mem_top
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨w, hw, rfl⟩ := hj
  have hc : ρ b (ρ a w) = ρ a (ρ b w) := by
    change (ρ b * ρ a) w = (ρ a * ρ b) w
    rw [← map_mul, ← map_mul, hab.eq]
  simp only [map_add, hc, hfix i hi, hfix w hw, map_one, Module.End.one_apply]

/-- If a component stabilizes the summands, its intersection with an abelian
quadratic actor exchanging them is trivial. This applies to a faithful
natural-plus-dual constituent without changing the acting group. -/
theorem quadratic_pair_component_inf_eq_bot (hfaith : Function.Injective ρ)
    (I : Submodule (ZMod 2) V) (K A : Subgroup G) [IsMulCommutative A]
    (hq : IsQuadratic ρ A) {a : G} (ha : a ∈ A)
    (hdis : Disjoint I (I.map (ρ a))) (hspan : I ⊔ I.map (ρ a) = ⊤)
    (hK : K ≤ subspaceStabilizer ρ I) : A ⊓ K = ⊥ := by
  apply bot_unique
  rintro b ⟨hb, hbK⟩
  apply Subgroup.mem_bot.mpr
  have hab : Commute b a := congrArg Subtype.val
    ((IsMulCommutative.is_comm (M := A)).comm (⟨b, hb⟩ : A) ⟨a, ha⟩)
  exact quadratic_pair_stabilizer_eq_one ρ hfaith I hq ha hb hab hdis hspan
    (fun v hv => (hK hbK v).2 hv)

end Representation.BinaryOffender
