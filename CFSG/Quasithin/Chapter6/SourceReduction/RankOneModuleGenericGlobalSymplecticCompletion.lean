module
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.SymplecticFour
public import Theory.GroupTheory.Amalgam.GeneratedCompletion.Overlap
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSymplecticMaximal

/-!
# The literal normalizer completion of a genuine symplectic extension

Let K be the whole residual of H. Compatible comparison of the actual
normalizer amalgam with a genuine symplectic extension, in either orientation,
constructs a faithful completion in X = N_G(L) ⊔ N_G(K). Its middle is the
literal intersection, and |X| ≤ |G| transfers the full extension order bound.
The native Cartan and unipotent groups retain their orders, normalization,
and trivial common fixed subgroup; the coset-graph action is faithful.

The existing pure amalgam comparison fixes the model exponent to the original
n and discharges the local conditions, including the field-four case. The
actual Chapter12 companion uses W = wholeReduced T L.

The five-path action and exact path counts now transfer to this literal
completion. The full extension bound bounds its vertex count and forces a
four-path collision. The new geometry theorem proves geodesicity, a generalized
quadrangle and equality of the full extension orders. The resulting equality
forces the normalizer join to be all of G and constructs the completion in
ambient G with its literal endpoint ranges. The marked Cartan apartment now
recognizes its normal Sp₄ subgroup; ambient simplicity makes this all of G,
proving IsPSp G 2 (2^n). The Chapter12 companion gives GlobalExit.
The separate source producer owns the compatible extension and ambient-order
inputs; generic-global retains their final discharge.

Source: Aschbacher–Smith F.4.3–6, F.4.10, F.4.16, F.4.24 and 5.3.2–4,
printed pp.274–279,282,287–288,657–659 of `refs/quasithin.pdf`.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterF.SourceCompletion.SymplecticFour
namespace SymplecticCompletion
variable {G : Type*} [Group G]

/-- The two actual normalizers and their entire intersection. -/
abbrev diagram (L K : Subgroup G) :=
  RankTwoAmalgam.ofSubgroups (normalizerAmalgam L K).M₁ (normalizerAmalgam L K).M₁₂
    (normalizerAmalgam L K).M₂ (normalizerAmalgam L K).middle_left
    (normalizerAmalgam L K).middle_right

abbrev join (L K : Subgroup G) : Subgroup G :=
  normalizer (L : Set G) ⊔ normalizer (K : Set G)

def original (L K : Subgroup G) : RankTwoAmalgam.FaithfulCompletion (diagram L K) (G := join L K) :=
  RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups _ _ _ inf_le_left inf_le_right

theorem original_overlap (L K : Subgroup G) :
    (original L K).left.range ⊓ (original L K).right.range = (original L K).middle.range :=
  RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_overlap _ _

variable {F : Type*} [Field F] {E : SourceExtension F} {L K : Subgroup G}

def ofIso (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam) : Completion E (join L K) :=
  (original L K).comapIso e.symm

def ofIsoReverse (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam.reverse) :
    Completion E (join L K) :=
  ((original L K).comapIso e.symm).reverse

/-- The direct marking retains the literal left injection into the join. -/
theorem ofIso_left (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam) (x : E.left) :
    ((ofIso e).left x : G) = (e.left.symm x).val :=
  RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left _ _ _ _ _ _

theorem ofIso_right (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam) (x : E.right) :
    ((ofIso e).right x : G) = (e.right.symm x).val :=
  RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right _ _ _ _ _ _

/-- The reversed marking exchanges the endpoint maps, not their common Borel. -/
theorem ofIsoReverse_left (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam.reverse) (x : E.left) :
    ((ofIsoReverse e).left x : G) = (e.right.symm x).val :=
  RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_right _ _ _ _ _ _

theorem ofIsoReverse_right (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam.reverse) (x : E.right) :
    ((ofIsoReverse e).right x : G) = (e.left.symm x).val :=
  RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_left _ _ _ _ _ _

theorem ofIso_overlap (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam) :
    (ofIso e).left.range ⊓ (ofIso e).right.range = (ofIso e).middle.range := by
  simpa only [ofIso,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using original_overlap L K

theorem ofIsoReverse_overlap (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam.reverse) :
    (ofIsoReverse e).left.range ⊓ (ofIsoReverse e).right.range = (ofIsoReverse e).middle.range := by
  apply RankTwoAmalgam.FaithfulCompletion.reverse_overlap
  simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
    RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using original_overlap L K

theorem ofIso_middle_range (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam) :
    (ofIso e).middle.range = (normalizer (L : Set G) ⊓ normalizer (K : Set G)).subgroupOf (join L K) := by
  rw [ofIso,RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range]
  exact RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_middle_range _ _ _ _ _

theorem ofIsoReverse_middle_range (e : RankTwoAmalgam.Iso (diagram L K) E.amalgam.reverse) :
    (ofIsoReverse e).middle.range = (normalizer (L : Set G) ⊓ normalizer (K : Set G)).subgroupOf (join L K) := by
  exact (congrArg MonoidHom.range
    (RankTwoAmalgam.FaithfulCompletion.reverse_middle ((original L K).comapIso e.symm))).trans
    ((RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range (original L K) e.symm).trans
      (RankTwoAmalgam.FaithfulCompletion.ofGeneratedSubgroups_middle_range _ _ _ _ _))

theorem card_le [Finite G] (hcard : Nat.card G ≤ Nat.card E.carrier) :
    Nat.card (join L K) ≤ Nat.card E.carrier :=
  (Nat.card_le_card_of_injective (join L K).subtype (join L K).subtype_injective).trans hcard
end SymplecticCompletion

/-- The genuine extension input and the ambient order bound give a faithful
completion in the actual normalizer join, with all recognition inputs that
are established here: the full overlap, the original field, and the marked
Cartan's trivial unipotent fixed subgroup. Small-completion recognition is
not asserted by this preparation theorem. -/
theorem Preparation.symplectic_extension_completion
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        c.middle.range.normalCore = ⊥ ∧
        Function.Injective (MulAction.toPermHom (SymplecticCompletion.join L (residual H))
          (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily)) ∧
        Nat.card c.unipotentMap.range = Nat.card F ^ 4 ∧
        Nat.card c.torusMap.range = (Nat.card F - 1)^2 ∧
        c.torusMap.range ≤ normalizer (c.unipotentMap.range : Set (SymplecticCompletion.join L (residual H))) ∧
        c.unipotentMap.range ⊓ centralizer (c.torusMap.range : Set (SymplecticCompletion.join L (residual H))) = ⊥ := by
  have hmn := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hFn : Nat.card F = 2^n := hmn ▸ hF
  have hq : 2 < Nat.card F := by
    rw [hFn]
    exact (by decide : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) h.exponent
  refine ⟨hmn,hFn,d.symplectic_normalizer_local_conditions h hH hp F hm hF he,?_⟩
  rcases hext with hext | hext
  · obtain ⟨e⟩ := hext
    exact ⟨SymplecticCompletion.ofIso e,SymplecticCompletion.ofIso_middle_range e,
      SymplecticCompletion.ofIso_overlap e,SymplecticCompletion.card_le hcard,
      Completion.middle_normalCore _,
      Completion.vertex_action_injective _ (SymplecticCompletion.ofIso_overlap e),
      Completion.card_unipotent_range _,Completion.card_torus_range _,
      Completion.torus_normalizes_unipotent _,Completion.unipotent_inf_centralizer_torus _ hq⟩
  · obtain ⟨e⟩ := hext
    exact ⟨SymplecticCompletion.ofIsoReverse e,SymplecticCompletion.ofIsoReverse_middle_range e,
      SymplecticCompletion.ofIsoReverse_overlap e,SymplecticCompletion.card_le hcard,
      Completion.middle_normalCore _,
      Completion.vertex_action_injective _ (SymplecticCompletion.ofIsoReverse_overlap e),
      Completion.card_unipotent_range _,Completion.card_torus_range _,
      Completion.torus_normalizes_unipotent _,Completion.unipotent_inf_centralizer_torus _ hq⟩

/-- The actual normalizer completion has the proved five-path action and
native path census. The full extension bound forces a four-path collision
at every root. This retains both orientations and the whole residual;
geodesicity and symplectic identification are not asserted here. -/
theorem Preparation.symplectic_extension_paths
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      ∃ c : Completion E (SymplecticCompletion.join L (residual H)),
        c.middle.range = (normalizer (L : Set G) ⊓ normalizer (residual H : Set G)).subgroupOf
          (SymplecticCompletion.join L (residual H)) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        Nat.card (SymplecticCompletion.join L (residual H)) ≤ Nat.card E.carrier ∧
        Nat.card (Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily) ≤
          2 * (Nat.card F + 1) * (Nat.card F ^ 2 + 1) ∧
        ∀ v : Subgroup.CosetGeometry.RankTwo.Vertex c.cosetFamily,
          SimpleGraph.PathTransitivePolygon.RootPathTransitive
            (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily)
            (SymplecticCompletion.join L (residual H)) v 5 ∧
          (∀ k : ℕ, Nat.card {p : SimpleGraph.BasedWalk
            (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily) (k+1) v // p.Nonbacktracking} =
              (Nat.card F + 1) * Nat.card F ^ k) ∧
          ∃ p q : SimpleGraph.BasedWalk (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily) 4 v,
            p.Nonbacktracking ∧ q.Nonbacktracking ∧ p ≠ q ∧ p.endpoint = q.endpoint := by
  obtain ⟨hmn,hFn,hlocal,c,hmid,ho,hbound,_⟩ :=
    d.symplectic_extension_completion h hH hp F hm hF he E hext hcard
  have hq : 2 < Nat.card F := by
    rw [hFn]
    exact (by decide : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) h.exponent
  refine ⟨hmn,hFn,hlocal,c,hmid,ho,hbound,c.card_vertices_le hbound,?_⟩
  intro v
  exact ⟨c.all_rootPathTransitive_five ho v,(fun k => c.card_paths ho k v),
    c.four_path_collision ho hq hbound v⟩
namespace SymplecticCompletion
variable {G : Type*} [Group G] {L K : Subgroup G}

/-- After generation is proved, the original inclusions give a completion in G itself. -/
def ambient (hgen : join L K = ⊤) : RankTwoAmalgam.FaithfulCompletion (diagram L K) (G := G) :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups _ _ _ inf_le_left inf_le_right hgen

theorem ambient_middle (hgen : join L K = ⊤) :
    (ambient hgen).middle.range = normalizer (L : Set G) ⊓ normalizer (K : Set G) := by
  change (normalizer (L : Set G) ⊓ normalizer (K : Set G)).subtype.range = _
  exact range_subtype _

theorem ambient_overlap (hgen : join L K = ⊤) :
    (ambient hgen).left.range ⊓ (ambient hgen).right.range = (ambient hgen).middle.range := by
  rw [ambient_middle]
  change (normalizer (L : Set G)).subtype.range ⊓ (normalizer (K : Set G)).subtype.range = _
  rw [range_subtype,range_subtype]

variable [Finite G] {F : Type*} [Field F] [Finite F] [CharP F 2] {E : SourceExtension F}

/-- The full extension order bound forces the original normalizer join to be
all of G. The compatible maps then give a faithful completion in ambient G,
with their original full intersection and endpoint ranges in either orientation. -/
theorem ambient_of_extension (hq : 2 < Nat.card F)
    (hext : Nonempty (RankTwoAmalgam.Iso (diagram L K) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso (diagram L K) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    join L K = ⊤ ∧ Nat.card G = Nat.card E.carrier ∧
    ∃ c : Completion E G,
      c.middle.range = normalizer (L : Set G) ⊓ normalizer (K : Set G) ∧
      c.left.range ⊓ c.right.range = c.middle.range ∧
      ((c.left.range = normalizer (L : Set G) ∧ c.right.range = normalizer (K : Set G)) ∨
       (c.left.range = normalizer (K : Set G) ∧ c.right.range = normalizer (L : Set G))) := by
  have hj : Nat.card (join L K) = Nat.card E.carrier := by
    rcases hext with hdir | hrev
    · obtain ⟨e⟩ := hdir
      exact (ofIso e).card_eq (ofIso_overlap e) hq (card_le hcard)
    · obtain ⟨e⟩ := hrev
      exact (ofIsoReverse e).card_eq (ofIsoReverse_overlap e) hq (card_le hcard)
  have hgen : join L K = ⊤ := Subgroup.eq_top_of_le_card _ (hcard.trans_eq hj.symm)
  have hcG : Nat.card G = Nat.card E.carrier := by
    apply le_antisymm hcard
    rw [←hj]
    exact Nat.card_le_card_of_injective (join L K).subtype (join L K).subtype_injective
  refine ⟨hgen,hcG,?_⟩
  rcases hext with hdir | hrev
  · obtain ⟨e⟩ := hdir
    let c := (ambient hgen).comapIso e.symm
    refine ⟨c,?_,?_,Or.inl ⟨?_,?_⟩⟩
    · exact (RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range _ _).trans (ambient_middle hgen)
    · simpa only [c,RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using ambient_overlap hgen
    · change ((ambient hgen).comapIso e.symm).left.range = _
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]
      exact range_subtype _
    · change ((ambient hgen).comapIso e.symm).right.range = _
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]
      exact range_subtype _
  · obtain ⟨e⟩ := hrev
    let c := ((ambient hgen).comapIso e.symm).reverse
    have hm : c.middle.range = normalizer (L : Set G) ⊓ normalizer (K : Set G) :=
      (congrArg MonoidHom.range (RankTwoAmalgam.FaithfulCompletion.reverse_middle _)).trans
        ((RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range _ _).trans (ambient_middle hgen))
    refine ⟨c,hm,?_,Or.inr ⟨?_,?_⟩⟩
    · apply RankTwoAmalgam.FaithfulCompletion.reverse_overlap
      simpa only [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_right_range,
        RankTwoAmalgam.FaithfulCompletion.comapIso_middle_range] using ambient_overlap hgen
    · change ((ambient hgen).comapIso e.symm).right.range = _
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_right_range]
      exact range_subtype _
    · change ((ambient hgen).comapIso e.symm).left.range = _
      rw [RankTwoAmalgam.FaithfulCompletion.comapIso_left_range]
      exact range_subtype _
end SymplecticCompletion

/-- The original source hypotheses and genuine extension/order inputs yield
ambient generation, exact full-extension order, and the actual generalized
quadrangle. Native symplectic identification remains a separate obligation. -/
theorem Preparation.symplectic_extension_geometry
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m = n ∧ Nat.card F = 2^n ∧
      Chapter5.Section03GreenExtension.SourceLocalConditions
        (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) ∧
      SymplecticCompletion.join L (residual H) = ⊤ ∧ Nat.card G = Nat.card E.carrier ∧
      ∃ c : Completion E G,
        c.middle.range = normalizer (L : Set G) ⊓ normalizer (residual H : Set G) ∧
        c.left.range ⊓ c.right.range = c.middle.range ∧
        ((c.left.range = normalizer (L : Set G) ∧ c.right.range = normalizer (residual H : Set G)) ∨
         (c.left.range = normalizer (residual H : Set G) ∧ c.right.range = normalizer (L : Set G))) ∧
        (∀ v (p : (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily).Walk v v),
          p.IsCycle → 8 ≤ p.length) ∧
        (∀ v w, (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily).dist v w ≤ 4) ∧
        (∃ v, ∃ p : (Subgroup.CosetGeometry.RankTwo.graph c.cosetFamily).Walk v v,
          p.IsCycle ∧ p.length = 8) := by
  have hmn := (d.symplectic_amalgam_blocks h hH.1.1.2 hp F hm hF he).1
  have hFn : Nat.card F = 2^n := hmn ▸ hF
  have hq : 2 < Nat.card F := by
    rw [hFn]
    exact (by decide : 2 = 2^1) ▸ Nat.pow_lt_pow_right (by decide) h.exponent
  obtain ⟨hgen,horder,c,hmid,ho,hends⟩ :=
    SymplecticCompletion.ambient_of_extension hq hext hcard
  exact ⟨hmn,hFn,d.symplectic_normalizer_local_conditions h hH hp F hm hF he,
    hgen,horder,c,hmid,ho,hends,c.quadrangle ho hq hcard⟩
/-- The genuine compatible extension and its full ambient order bound recognize
G as PSp₄ at the original exponent. The source preparation, whole residual and
both orientations are unchanged; no geometric or generation premise is added. -/
theorem Preparation.symplectic_extension_recognition
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse))
    (E : SourceExtension F)
    (hext : Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam) ∨
      Nonempty (RankTwoAmalgam.Iso
      (SymplecticCompletion.diagram L (residual H)) E.amalgam.reverse))
    (hcard : Nat.card G ≤ Nat.card E.carrier) :
    m=n ∧ Nat.card F=2^n ∧
      SymplecticCompletion.join L (residual H)=⊤ ∧ Nat.card G=Nat.card E.carrier ∧
      ClassicalGroup.IsPSp G 2 (2^n) := by
  obtain ⟨hmn,hFn,_hlocal,hgen,horder,c,_hmid,ho,_hends,_hgeom⟩ :=
    d.symplectic_extension_geometry h hH hp F hm hF he E hext hcard
  let : IsSimpleGroup G := h.qtke.simple
  obtain ⟨a⟩ := c.nonempty_mulEquiv_native_of_simple hFn h.exponent ho hcard
  exact ⟨hmn,hFn,hgen,horder,F,inferInstance,inferInstance,hFn,
    ⟨a.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv⟩⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
