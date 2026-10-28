module

public import Theory.GroupTheory.Amalgam.UniquenessSystem.Recognition
public import Theory.SpecificGroups.Janko4.Model

/-!
# Gluing equivalent uniqueness systems with two cycle bases

Apply universal completion in both directions. The resulting homomorphisms
are inverse because their composites fix the generating vertex and local
groups. Thus bases for both systems remove the need for a separate simplicity
theorem. The final specialization has the literal binary J₄ carrier as target.

These conditional results are the final gluing step only. For type-J₄
recognition, the source-specific systems, their equivalent local maps, and
their cycle bases must still be constructed from `IsTypeJ4`.

Source: Aschbacher–Segev, *Extending morphisms of groups and graphs*, Ann.
Math. 135 (1992), 297–323; *The study of J₄ via the theory of uniqueness
systems*, pp.19–21. The existing universal completion implements the path
presentation argument, and the proof here uses its local restrictions.
-/

@[expose] public section

namespace Theory.GroupTheory.Recognition.JankoFour

open GraphUniquenessSystem

universe u v u' v'
variable {G : Type u} {V : Type v} [Group G] [MulAction G V]
variable {G' : Type u'} {V' : Type v'} [Group G'] [MulAction G' V']

/-- Two cycle bases extend equivalent local maps to an ambient isomorphism,
with the original local maps retained. No simplicity assumption is used. -/
theorem exists_mulEquiv_of_equivalent_bases
    {U : System G V} {U' : System G' V'} (s : Similarity U U')
    (hs : s.IsEquivalence) (hb : U.IsBase) (hb' : U'.IsBase) :
    ∃ e : G ≃* G',
      (∀ a : U.vertexGroup, e a = (s.vertexIso a : G')) ∧
      (∀ a : U.H, e a = (s.localIso a : G')) := by
  obtain ⟨f⟩ := s.nonempty_extension_of_isEquivalence_of_isBase hs hb'
  obtain ⟨g⟩ := s.symm.nonempty_extension_of_isEquivalence_of_isBase
    (s.isEquivalence_symm hs) hb
  have gv (a : U.vertexGroup) : g.hom a = (s.vertexIso a : G') := by
    simpa only [Similarity.symm, MulEquiv.symm_apply_apply] using
      g.onVertex (s.vertexIso a)
  have gh (a : U.H) : g.hom a = (s.localIso a : G') := by
    simpa only [Similarity.symm, MulEquiv.symm_apply_apply] using
      g.onLocal (s.localIso a)
  have hfg : f.hom.comp g.hom = MonoidHom.id G := by
    apply U.hom_ext
    · intro a
      change f.hom (g.hom a) = a
      rw [gh, f.onLocal]
    · intro a
      change f.hom (g.hom a) = a
      rw [gv, f.onVertex]
  have hgf : g.hom.comp f.hom = MonoidHom.id G' := by
    apply U'.hom_ext
    · intro a
      obtain ⟨a, rfl⟩ := s.localIso.surjective a
      change g.hom (f.hom (s.localIso a)) = s.localIso a
      rw [f.onLocal, gh]
    · intro a
      obtain ⟨a, rfl⟩ := s.vertexIso.surjective a
      change g.hom (f.hom (s.vertexIso a)) = s.vertexIso a
      rw [f.onVertex, gv]
  let e : G ≃* G' :=
    { toFun := g.hom
      invFun := f.hom
      left_inv := fun a => DFunLike.congr_fun hfg a
      right_inv := fun a => DFunLike.congr_fun hgf a
      map_mul' := g.hom.map_mul }
  exact ⟨e, gv, gh⟩

/-- Application of the gluing step to the project's concrete J₄ carrier.
The J₄ geometry and its source comparison remain explicit obligations. -/
theorem recognize_of_equivalent_bases
    {W : Type*} [MulAction Janko4.Model W]
    {U : System G V} {U₄ : System Janko4.Model W}
    (s : Similarity U U₄) (hs : s.IsEquivalence)
    (hb : U.IsBase) (hb₄ : U₄.IsBase) : Nonempty (G ≃* Janko4.Model) := by
  obtain ⟨e, _, _⟩ := exists_mulEquiv_of_equivalent_bases s hs hb hb₄
  exact ⟨e⟩

end Theory.GroupTheory.Recognition.JankoFour
