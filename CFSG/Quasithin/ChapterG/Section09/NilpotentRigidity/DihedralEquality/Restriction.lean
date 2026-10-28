module

public import CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.Contracts

/-!
# Restricting the spaces in the dihedral equality induction

Commuting actors preserve rotation displacement spaces and fixed spaces.
Faithfulness descends to a summand with pointwise fixed complement, and to
one half of a sum of two commuting translates. When a complement is fixed,
the restricted displacement space maps onto the ambient displacement space
under its actual inclusion. This last identity is essential for gluing the
internal decompositions, whose summands cannot be replaced by isomorphic
but unrelated subspaces.

These are linear-algebra steps in Aschbacher--Smith G.9.2, printed
pp.352--353. The product-kernel argument establishing the initial faithful
restrictions is a separate obligation.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- Centralizing the actors preserves their actual displacement span. -/
theorem movedSpace_stable_of_commute (K : Subgroup G) (g : G)
    (hc : ∀ k : K, Commute g (k : G)) :
    movedSpace ρ K ≤ (movedSpace ρ K).comap (ρ g) := by
  change Submodule.span (ZMod 2)
    (Set.range fun kv : K × V => ρ kv.1 kv.2 - kv.2) ≤ _
  apply Submodule.span_le.mpr
  rintro v ⟨⟨k, w⟩, rfl⟩
  change ρ g (ρ k w - w) ∈ movedSpace ρ K
  have he : ρ g (ρ k w) = ρ k (ρ g w) := by
    change (ρ g * ρ k) w = (ρ k * ρ g) w
    rw [← map_mul, ← map_mul, (hc k).eq]
  rw [map_sub, he]
  exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp K.subtype) k (ρ g w)

/-- A commuting actor preserves the fixed space of an element. -/
theorem fixedSpace_stable_of_commute {g x : G} (hc : Commute g x) :
    LinearMap.ker (ρ x - 1) ≤ (LinearMap.ker (ρ x - 1)).comap (ρ g) := by
  intro v hv
  have hv' : ρ x v = v := sub_eq_zero.mp hv
  change ρ x (ρ g v) - ρ g v = 0
  have he : ρ x (ρ g v) = ρ g (ρ x v) := by
    change (ρ x * ρ g) v = (ρ g * ρ x) v
    rw [← map_mul, ← map_mul, hc.eq]
  rw [he, hv', sub_self]

/-- Equality on two spanning subspaces is equality on the module. -/
theorem linearMap_eq_of_sup {W C : Submodule (ZMod 2) V} (h : W ⊔ C = ⊤)
    {f g : V →ₗ[ZMod 2] V}
    (hW : ∀ v : W, f v = g v) (hC : ∀ v : C, f v = g v) : f = g := by
  ext v
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ W ⊔ C by rw [h]; trivial)
  rw [map_add, map_add, hW ⟨w, hw⟩, hC ⟨c, hc⟩]

/-- A faithful representation remains faithful on a spanning summand
when the complementary summand is fixed pointwise. -/
theorem faithful_subrepresentation_of_fixed_complement
    (hfaith : Function.Injective ρ) {W C : Submodule (ZMod 2) V}
    (hW : ∀ g, W ≤ W.comap (ρ g)) (hsup : W ⊔ C = ⊤)
    (hC : ∀ g (v : C), ρ g v = (v : V)) :
    Function.Injective (ρ.subrepresentation W hW) := by
  intro g h he
  apply hfaith
  apply linearMap_eq_of_sup hsup
  · intro v
    exact congrArg Subtype.val (congrArg (fun a : W →ₗ[ZMod 2] W => a v) he)
  · intro v
    rw [hC, hC]

/-- If a half-space and one commuting translate span the whole module,
faithfulness on the whole module descends to the half-space. -/
theorem faithful_subrepresentation_of_translate
    (hfaith : Function.Injective ρ) (W : Submodule (ZMod 2) V)
    (hW : ∀ g, W ≤ W.comap (ρ g)) (t : V →ₗ[ZMod 2] V)
    (ht : ∀ g, (ρ g).comp t = t.comp (ρ g))
    (hsup : W ⊔ W.map t = ⊤) :
    Function.Injective (ρ.subrepresentation W hW) := by
  intro g h he
  have heW (v : W) : ρ g v = ρ h v :=
    congrArg Subtype.val (congrArg (fun a : W →ₗ[ZMod 2] W => a v) he)
  apply hfaith
  apply linearMap_eq_of_sup hsup heW
  rintro ⟨v, hv⟩
  obtain ⟨w, hw, rfl⟩ := hv
  have hg := LinearMap.congr_fun (ht g) w
  have hh := LinearMap.congr_fun (ht h) w
  change ρ g (t w) = t (ρ g w) at hg
  change ρ h (t w) = t (ρ h w) at hh
  rw [hg, hh, heW ⟨w, hw⟩]

/-- On a direct summand whose complement is fixed by `K`, the restricted
and ambient displacement spans agree under the actual inclusion. -/
theorem movedSpace_subrepresentation_map_of_fixed_complement
    {W C : Submodule (ZMod 2) V} (hW : ∀ g, W ≤ W.comap (ρ g))
    (hsup : W ⊔ C = ⊤) (K : Subgroup G)
    (hC : ∀ g : K, ∀ v : C, ρ g v = (v : V)) :
    (movedSpace (ρ.subrepresentation W hW) K).map W.subtype = movedSpace ρ K := by
  apply le_antisymm
  · rw [movedSpace, Representation.Coinvariants.ker, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro v ⟨w, ⟨⟨g, u⟩, rfl⟩, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker (ρ := ρ.comp K.subtype) g u
  · apply Submodule.span_le.mpr
    rintro v ⟨⟨g, u⟩, rfl⟩
    obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.mp
      (show u ∈ W ⊔ C by rw [hsup]; trivial)
    have hc' := hC g ⟨c, hc⟩
    change ρ g c = c at hc'
    have he : ρ g (w + c) - (w + c) = ρ g w - w := by
      rw [map_add, hc']; abel
    change ρ g (w + c) - (w + c) ∈ _
    rw [he]
    refine ⟨(ρ.subrepresentation W hW) g ⟨w, hw⟩ - ⟨w, hw⟩, ?_, rfl⟩
    exact Representation.Coinvariants.sub_mem_ker
      (ρ := (ρ.subrepresentation W hW).comp K.subtype) g ⟨w, hw⟩

end CFSG.Quasithin.ChapterG.Section09.NilpotentRigidity.DihedralEquality
