module
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.FirstBaumann
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneCoordinates
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The opposite singular line in a first Baumann member of order four

The actual alpha splitting and trivial common Sylow centralizer make an
order-four first member project onto the opposite natural fixed plane.
An actual alternating conjugation exchanges the two nonsingular plane
vectors. Both lifts centralize Baum(T), so first-member fusion keeps them
in the same first member. Their product is the opposite singular line.
The original natural modules are consequently disjoint.

This strengthens the order-four branch of the original opposite-normalizer
configuration. It does not produce a residual elementary lift or exclude
the order-two first member. Source: Aschbacher--Smith 13.2.4(2b),13.2.8(1),
pp.879--880, and C.1.18,C.1.24(a), pp.126,130--131.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source ChapterB ChapterC
open Section06.CentralizerReduction
open BinaryPermutation.FiveCentralizerGeometry BinaryPermutation.AlternatingFiveFlag
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H K W W₁ W₂ W₃ : Subgroup G}

private theorem first_fixed_component
    (d : Context T L V V₁ V₂ V₃)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer
      (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) :
    D.first.map (baumann (T : Subgroup G)).subtype ≤ centralizer (L : Set G) := by
  let A := D.first.map (baumann (T : Subgroup G)).subtype
  have hBC := GlaubermanNiles.image_centralizes_of_le_omegaCenter
    (baumann (T : Subgroup G)).subtype D.first D.first_le_omegaCenter
  rw [range_subtype] at hBC
  have hJC : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (A : Set G) :=
    (elementaryAbelianMaxJ_le_baumann _).trans hBC
  have hLN := (le_sup_left.trans hn).trans (normalizer_le_normalizer_centralizer A)
  apply le_centralizer_iff.mp
  rw [d.eq_thompson_commutator_of_moves hJ]
  exact (commutator_mono le_rfl hJC).trans
    ((commutator_comm L (centralizer (A : Set G))).le.trans
      (le_normalizer_iff_commutator_le_left.mp hLN))

/-- An order-four first member normalized by LT contains the opposite
natural module's original singular line. -/
theorem original_first_baumann_four_contains_opposite_line
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hA4 : Nat.card (D.first.map (baumann (T : Subgroup G)).subtype) = 4)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer
      (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) :
    W₁ ≤ D.first.map (baumann (T : Subgroup G)).subtype := by
  let A := D.first.map (baumann (T : Subgroup G)).subtype
  let E := thompsonAlpha (T : Subgroup G)
  let F := E ⊓ centralizer (K : Set G)
  have hAE : A ≤ E := by
    change A ≤ thompsonAlpha (T : Subgroup G)
    rw [←omegaCenter_baumann_eq_thompsonAlpha]
    exact map_mono D.first_le_omegaCenter
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  have hEC : E ≤ centralizer (baumann (T : Subgroup G) : Set G) := by
    change thompsonAlpha (T : Subgroup G) ≤ _
    rw [←omegaCenter_baumann_eq_thompsonAlpha]
    exact fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx).2.2
  have hAL := first_fixed_component d hJd D hn
  have hWT : W ⊓ centralizer (baumann (T : Subgroup G) : Set G) = W₂ := by
    apply (SourceAssembly.baumann_alternatives e).resolve_left
    exact fun h => hJe ((elementaryAbelianMaxJ_le_baumann _).trans (h.trans inf_le_right))
  have hE : E = F ⊔ W₂ := by
    have he := local_alpha_decomposition e hJe
    have hfix : W ⊓ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) = W₂ := by
      apply le_antisymm
      · exact (le_inf inf_le_left ((le_sup_right.trans he.ge).trans hEC)).trans hWT.le
      · exact le_inf e.flag.two_le_V
          ((hWT.ge.trans inf_le_right).trans (centralizer_le (elementaryAbelianMaxJ_le_baumann _)))
    simpa only [hfix] using he
  have hAF : Disjoint A F := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact (common_sylow_centralizer_eq_bot d hH e.normalizes_L hjoin).le
      ⟨⟨((map_subtype_le _).trans inf_le_left) hx.1,hAL hx.1⟩,hx.2.2⟩
  have hFW : Disjoint F W₂ := by
    apply disjoint_iff.mpr
    apply bot_unique
    intro x hx
    exact e.flag.module.fixed_eq_bot.le ⟨e.flag.two_le_V hx.2,hx.1.2⟩
  have hFA : F ≤ normalizer (A : Set G) :=
    (inf_le_left.trans ((le_centralizer E).trans (centralizer_le hAE))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hWF : W₂ ≤ normalizer (F : Set G) :=
    ((le_sup_right.trans hE.ge).trans ((le_centralizer E).trans (centralizer_le inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hspan : A ⊔ F = E := by
    apply eq_of_le_of_card_ge (sup_le hAE inf_le_left)
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A F hFA hAF]
    have hc := card_sup_eq_mul_of_normalizes_of_disjoint F W₂ hWF hFW
    rw [←hE,e.flag.two_card] at hc
    rw [hc,hA4]
    omega
  obtain ⟨s,hline,hplane,_⟩ := e.plane_third_coordinates
  have hvE : s.map (Multiplicative.ofAdd v) ∈ E :=
    (le_sup_right.trans hE.ge) (hplane.le (mem_map_of_mem s.map (Or.inr (Or.inr (Or.inl rfl)))))
  have hvAF : s.map (Multiplicative.ofAdd v) ∈ (A : Set G) * (F : Set G) := by
    rw [←coe_mul_of_right_le_normalizer_left A F hFA,hspan]
    exact hvE
  obtain ⟨a,ha,c,hc,hac⟩ := hvAF
  obtain ⟨g,hg⟩ := nonline_transitive (Multiplicative.ofAdd v)
    (Multiplicative.ofAdd (z+v)) (by rfl) (by decide +kernel)
    (by rfl) (by decide +kernel)
  obtain ⟨k,hk⟩ := s.onto g.val
  have he : (k:G) * s.map (Multiplicative.ofAdd v) * (k:G)⁻¹ =
      s.map (Multiplicative.ofAdd (z+v)) := by
    have hh := s.equivariant k v
    rw [hk] at hh
    exact hh.trans (congrArg s.map hg)
  have hkc : (k:G) * c * (k:G)⁻¹ = c :=
    mul_inv_eq_iff_eq_mul.mpr (hc.2 k k.property)
  have haeq : a = s.map (Multiplicative.ofAdd v) * c⁻¹ := by
    rw [←hac]
    group
  have hconj : (k:G) * a * (k:G)⁻¹ =
      s.map (Multiplicative.ofAdd (z+v)) * c⁻¹ := by
    rw [haeq]
    calc
      _ = ((k:G) * s.map (Multiplicative.ofAdd v) * (k:G)⁻¹) *
          ((k:G) * c * (k:G)⁻¹)⁻¹ := by group
      _ = _ := by rw [he,hkc]
  have hy : s.map (Multiplicative.ofAdd (z+v)) * c⁻¹ ∈
      centralizer (baumann (T : Subgroup G) : Set G) := by
    apply mul_mem
    · exact hEC ((le_sup_right.trans hE.ge)
        (hplane.le (mem_map_of_mem s.map (Or.inr (Or.inr (Or.inr rfl))))))
    · exact inv_mem (hEC hc.1)
  have hyA : s.map (Multiplicative.ofAdd (z+v)) * c⁻¹ ∈ A :=
    first_baumann_fusion_closed D ha hy (isConj_iff.mpr ⟨k,hconj⟩)
  have hzA : s.map (Multiplicative.ofAdd z) ∈ A := by
    have hm := A.mul_mem hyA (A.inv_mem ha)
    rw [haeq] at hm
    have hp : (s.map (Multiplicative.ofAdd (z+v)) * c⁻¹) *
        (s.map (Multiplicative.ofAdd v) * c⁻¹)⁻¹ = s.map (Multiplicative.ofAdd z) := by
      calc
        _ = s.map (Multiplicative.ofAdd (z+v)) * (s.map (Multiplicative.ofAdd v))⁻¹ := by group
        _ = s.map (Multiplicative.ofAdd z) := by
          rw [←map_inv,←map_mul]
          congr 1
          change Multiplicative.ofAdd ((z+v)+ -v) = Multiplicative.ofAdd z
          rw [add_neg_cancel_right]
    exact hp ▸ hm
  rw [←hline,MonoidHom.map_zpowers]
  exact zpowers_le.mpr hzA

private theorem line_le_normalized_intersection
    (e : Context T K W W₁ W₂ W₃) {A : Subgroup G}
    (hAW : A ≤ W) (hne : A ≠ ⊥)
    (hn : (T : Subgroup G) ≤ normalizer (A : Set G)) : W₁ ≤ A := by
  have hmeet := inf_centerIn_ne_bot T.isPGroup' hne (hAW.trans e.chosen.le_sylow) hn
  have hle : A ⊓ centerIn (T : Subgroup G) ≤ W₁ := by
    rw [←e.flag.module_fixed_eq_line]
    exact le_inf (inf_le_left.trans hAW) (inf_le_right.trans inf_le_right)
  have hc : Nat.card (A ⊓ centerIn (T : Subgroup G) : Subgroup G) = 2 := by
    have hd := card_dvd_of_le hle
    rw [e.flag.one_card] at hd
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with hh | hh
    · exact (hmeet (eq_bot_of_card_le _ (by omega))).elim
    · exact hh
  have heq := eq_of_le_of_card_ge hle (by rw [e.flag.one_card,hc])
  exact heq.ge.trans inf_le_left

/-- In the order-four first-member branch the two original natural
modules have trivial intersection. -/
theorem original_first_baumann_four_modules_disjoint
    (d : Context T L V V₁ V₂ V₃) (e : Context T K W W₁ W₂ W₃)
    (hjoin : K ⊔ (T : Subgroup G) = H)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hJd : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hJe : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (D : GlaubermanNiles.CharacteristicPair (baumann (T : Subgroup G)))
    (hA4 : Nat.card (D.first.map (baumann (T : Subgroup G)).subtype) = 4)
    (hn : L ⊔ (T : Subgroup G) ≤ normalizer
      (D.first.map (baumann (T : Subgroup G)).subtype : Set G)) :
    Disjoint V W := by
  have hWC := (original_first_baumann_four_contains_opposite_line d e hjoin hH hJd hJe D hA4 hn).trans
    (first_fixed_component d hJd D hn)
  apply disjoint_iff.mpr
  by_contra hh
  have hline : W₁ ≤ V ⊓ W := line_le_normalized_intersection e inf_le_right hh
    ((le_inf d.flag.T_normalizes e.flag.T_normalizes).trans inf_normalizer_le_normalizer_inf)
  have hz : W₁ = ⊥ := bot_unique ((le_inf (hline.trans inf_le_left) hWC).trans
    d.flag.module.fixed_eq_bot.le)
  have hc := e.flag.one_card
  rw [hz,Nat.card_eq_fintype_card] at hc
  simp at hc

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
