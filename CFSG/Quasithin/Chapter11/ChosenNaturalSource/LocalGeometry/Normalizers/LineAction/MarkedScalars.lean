module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.ScalarGeometry
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Flags

/-!
# The scalar line action from the constructed marked flag

Inner uniqueness makes the full N_L(T_L) preserve the literal first flag
subgroup. When C_V(L)=1, its inner Sylow acts both by field scalars and by
two-elements, so its action is trivial. Nonzero-vector transitivity and
Sylow conjugacy then give transitivity on the line by N_L(T_L). The odd Hall
Cartan has the same image, hence acts by the full field scalar group.

This proves cyclicity, regularity and Sylow normalization without assuming
the preceding fixed-line equality. The original 11.2.3 consumer consequently
retains only Sylow-normalizer containment, the preceding residual/radical
centralization identities, and the radical-normalizer alternative. The first
remains with qt-d-1222-natural-line-action; the latter source inputs belong
to qt-d-1222-natural-normalizer-source and its preceding-source producers.

Source: Aschbacher--Smith, 11.0.2 and 11.2.3, printed pp.759--761,768--769.
-/

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped IsMulCommutative Pointwise
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers

private theorem marked_normalizer_transporter {H W : Type*} [Group H] [Finite H]
    [MulAction H W] (P : Sylow 2 H) (x y : W)
    (hx : ∀ p ∈ (P : Subgroup H), p • x = x)
    (hy : ∀ p ∈ (P : Subgroup H), p • y = y)
    (g : H) (hg : g • x = y) :
    ∃ n ∈ normalizer (P : Set H), n • x = y := by
  let C := MulAction.stabilizer H y
  have hP : (P : Subgroup H) ≤ C := hy
  have hQ : (g • P : Sylow 2 H) ≤ C := by
    rintro _ ⟨p,hp,rfl⟩
    change (g * p * g⁻¹) • y = y
    rw [← hg, mul_smul, mul_smul, inv_smul_smul, hx p hp]
  obtain ⟨h,hh⟩ := MulAction.exists_smul_eq C ((g • P).subtype hQ) (P.subtype hP)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  exact ⟨h * g, Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh), by
    rw [mul_smul, hg]
    exact h.property⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} (f : InvariantFlag c)

private theorem marked_normalizer_preserves_line :
    cartanNormalizer T L ≤ normalizer (f.Vi 0 : Set G) :=
  f.normalizer_le_flag_normalizer (SylowNormalizer.invariantFlag_geometry D S f).2.1 0

private theorem innerSylow_trivial_line_action
    (hz : V ⊓ centralizer (L : Set G) = ⊥)
    (g : G) (hg : g ∈ (T : Subgroup G) ⊓ L) :
    lineAction f ⟨g,f.invariant 0 hg.1⟩ = 1 := by
  let a := (lineAction f).comp (inclusion (f.invariant 0))
  let u : T := ⟨g,hg.1⟩
  have hmem : a u ∈ (lineScalars f hz).range :=
    lineImage_le_scalars f hz (H := (T : Subgroup G) ⊓ L) inf_le_right
      (mem_map_of_mem (lineAction f) hg)
  have hu : Odd (Nat.card S.field.Carrierˣ) := by
    rw [Nat.card_units,S.field.card_eq]
    apply Nat.Even.sub_odd (Nat.one_le_pow _ _ (by decide))
    · exact even_two.pow_of_ne_zero (by have := S.field.degree_pos; omega)
    · exact odd_one
  have hodd : Odd (Nat.card (lineScalars f hz).range) :=
    hu.of_dvd_nat (Subgroup.card_range_dvd (lineScalars f hz))
  obtain ⟨n,hn⟩ := T.isPGroup' u
  have htwo : orderOf (a u) ∣ 2^n := orderOf_dvd_of_pow_eq_one (by
    rw [←map_pow,hn,map_one])
  have ho : orderOf (a u) ∣ Nat.card (lineScalars f hz).range := by
    change orderOf ((⟨a u,hmem⟩ : (lineScalars f hz).range) :
      Additive (f.Vi 0) ≃ₗ[ZMod 2] Additive (f.Vi 0)) ∣ _
    rw [Subgroup.orderOf_coe]
    exact orderOf_dvd_natCard _
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_right.mpr hodd).pow_right n) ho htwo)

private theorem marked_line_transitive
    (hz : V ⊓ centralizer (L : Set G) = ⊥)
    (x y : f.space 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ n : cartanNormalizer T L,
      c.modelAction (c.quotientMap ⟨n,n.property.1⟩) x.val = y.val := by
  let ρ := c.modelAction.comp c.quotientMap
  let : MulAction L c.Space :=
    { smul := fun l v => ρ l v
      one_smul := by intro v; change ρ 1 v = v; simp
      mul_smul := by intro a b v; change ρ (a*b) v = ρ a (ρ b v); rw [map_mul]; rfl }
  have hfix (v : f.space 0) (p : L) (hp : p ∈ (c.innerSylow : Subgroup L)) : p • v.val = v.val := by
    obtain ⟨w,hw⟩ := lineProjection_surjective f v
    have hpT : p.val ∈ T := by rw [c.innerSylow_coe] at hp; exact hp
    have hh := lineProjection_component f p (f.invariant 0 hpT) w
    rw [innerSylow_trivial_line_action f hz p ⟨hpT,p.property⟩] at hh
    change c.modelAction (c.quotientMap p) v.val = v.val
    change (lineProjection f w).val =
      c.modelAction (c.quotientMap p) (lineProjection f w).val at hh
    rw [hw] at hh
    exact hh.symm
  obtain ⟨g,hg⟩ := model_transitive c x.val y.val
    (fun h => hx (Subtype.ext h)) (fun h => hy (Subtype.ext h))
  obtain ⟨l,hl⟩ := c.quotientMap_surjective g
  obtain ⟨n,hn,he⟩ := marked_normalizer_transporter c.innerSylow x.val y.val
    (hfix x) (hfix y) l (by change c.modelAction (c.quotientMap l) x.val = y.val; rw [hl]; exact hg)
  have hN : n.val ∈ cartanNormalizer T L := by
    rw [← componentNormalizer_map c.innerSylow c.innerSylow_coe]
    exact mem_map_of_mem _ hn
  exact ⟨⟨n,hN⟩,he⟩

private theorem marked_cartanSylow_fixes_line
    (hz : V ⊓ centralizer (L : Set G) = ⊥)
    (p : cartanNormalizer T L)
    (hp : p ∈ (cartanSylow c : Subgroup (cartanNormalizer T L))) :
    lineAction f (inclusion (marked_normalizer_preserves_line f) p) = 1 :=
  innerSylow_trivial_line_action f hz p (cartanSylow_le_intersection p hp)

private theorem marked_lineImage_cartan_eq_normalizer
    {X : Subgroup G} (hX : IsCartan T L X)
    (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    lineImage f X = lineImage f (cartanNormalizer T L) := by
  apply le_antisymm (map_mono (comap_mono hX.1))
  rintro _ ⟨n,hn,rfl⟩
  let n' : cartanNormalizer T L := ⟨n,hn⟩
  obtain ⟨⟨p,x⟩,he⟩ := (OddHall.sylow_complement_of_hall (cartanSylow c) hX.2).2 n'
  have he' : n = inclusion (marked_normalizer_preserves_line f) (p.val * x.val) :=
    Subtype.ext (congrArg (fun z : cartanNormalizer T L => (z : G)) he.symm)
  rw [he',map_mul,map_mul,marked_cartanSylow_fixes_line f hz p.val p.property,one_mul]
  exact mem_map_of_mem _ x.property

/-- The actual Cartan image is the full scalar group, using the constructed flag. -/
theorem marked_lineImage_eq_scalars {X : Subgroup G} (hX : IsCartan T L X)
    (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    lineImage f X = (lineScalars f hz).range := by
  apply le_antisymm (lineImage_le_scalars f hz (hX.1.trans inf_le_left))
  rintro _ ⟨a,rfl⟩
  let : Nontrivial (f.Vi 0) := (Subgroup.nontrivial_iff_ne_bot _).mpr (f.V_ne_bot 0)
  obtain ⟨v,hv⟩ := exists_ne (0 : Additive (f.Vi 0))
  let e := lineCoordinates f hz
  let w := lineScalars f hz a v
  have hw : w ≠ 0 := fun h => hv ((lineScalars f hz a).injective
    (h.trans (map_zero _).symm))
  obtain ⟨n,hn⟩ := marked_line_transitive f hz (e v) (e w)
    (fun h => hv (e.injective (h.trans e.map_zero.symm)))
    (fun h => hw (e.injective (h.trans e.map_zero.symm)))
  let n' := inclusion (marked_normalizer_preserves_line f) n
  have hnact : lineAction f n' v = w := by
    apply e.injective
    apply Subtype.ext
    exact (lineProjection_component f ⟨n,n.property.1⟩ n'.property v).trans hn
  have hnmem : lineAction f n' ∈ lineImage f (cartanNormalizer T L) := mem_map_of_mem _ n.property
  have hnscalar := lineImage_le_scalars f hz (H := cartanNormalizer T L) inf_le_left hnmem
  obtain ⟨z,_,hu⟩ := lineScalars_regular f hz v w hv hw
  have he : lineAction f n' = lineScalars f hz a := congrArg Subtype.val
    ((hu ⟨lineAction f n',hnscalar⟩ hnact).trans
      (hu ⟨lineScalars f hz a,MonoidHom.mem_range.mpr ⟨a,rfl⟩⟩ rfl).symm)
  rw [marked_lineImage_cartan_eq_normalizer f hX hz,←he]
  exact hnmem

/-- All three Singer inputs follow from the original marking and Cartan. -/
theorem marked_line_scalar_geometry {X : Subgroup G} (hX : IsCartan T L X)
    (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    IsCyclic (lineImage f X) ∧ LinearGroup.IsRegularOnNonzero (lineImage f X) ∧
      lineImage f T ≤ normalizer (lineImage f X : Set _) := by
  refine ⟨?_,?_,?_⟩
  · rw [marked_lineImage_eq_scalars f hX hz]
    exact lineScalars_isCyclic f hz
  · rw [marked_lineImage_eq_scalars f hX hz]
    exact lineScalars_regular f hz
  · rw [marked_lineImage_cartan_eq_normalizer f hX hz]
    apply le_trans (map_mono ?_) (((cartanNormalizer T L).subgroupOf
      (normalizer (f.Vi 0 : Set G))).le_normalizer_map (lineAction f))
    intro t ht
    rw [← subgroupOf_normalizer_eq (marked_normalizer_preserves_line f)]
    exact sylow_normalizes_cartanNormalizer (D := D) ht

/-- The exact zero-fixed-space normalization input of the 11.2.3 consumer. -/
theorem chosen_line_normalized_of_marked_flag {X : Subgroup G} (hX : IsCartan T L X)
    (hz : V ⊓ centralizer (L : Set G) = ⊥) :
    normalizer (f.Vi 0 : Set G) ≤
      normalizer ((centralizer (f.Vi 0 : Set G) ⊔ X ⊔ (T : Subgroup G) : Subgroup G) : Set G) := by
  obtain ⟨hcyc,hreg,hTN⟩ := marked_line_scalar_geometry f hX hz
  exact chosen_line_normalized_of_singer f hX
    (SylowNormalizer.cartan_le_line_normalizer D S f hX) hcyc hreg hTN

/-- The original two source clauses with scalar geometry and residual models discharged. -/
theorem chosen_source_11_2_3_of_marked_line
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c)
    {X : Subgroup G} (hX : IsCartan T L X)
    (hfix : f.Li 0 ≤ centralizer (f.Vi 0 : Set G))
    (hfixR : f.Ri 0 ≤ centralizer (f.Vi 0 : Set G))
    (hNT : normalizer (T : Set G) ≤ normalizer (L : Set G))
    (hradical : Source.RadicalNormalizerAlternative (T : Subgroup G) V (f.Vi 0) (f.Ri 0)
      (normalizer (L : Set G)) L S.field.degree) :
    (V ⊓ centralizer (L : Set G) = ⊥ →
      normalizer (f.Vi 0 : Set G) = centralizer (f.Vi 0 : Set G) ⊔
        (normalizer (L : Set G) ⊓ normalizer (f.Vi 0 : Set G))) ∧
    (centralizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G) →
      normalizer (f.Vi 0 : Set G) ≤ normalizer (L : Set G)) := by
  have hXU := SylowNormalizer.cartan_le_line_normalizer D S f hX
  apply chosen_source_11_2_3_of_action_steps D S f hX hXU hNT _ _ hradical
  · intro hz
    exact chosen_line_normalized_of_marked_flag f hX hz
  · intro _ hC
    exact chosen_line_positive_steps_of_flag_geometry S f
      ((SylowNormalizer.invariantFlag_geometry D S f).2.2.model 0) hfix hfixR hC
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers
