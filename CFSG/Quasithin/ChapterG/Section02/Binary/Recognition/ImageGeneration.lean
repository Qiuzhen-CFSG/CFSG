module
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Transport
public import CFSG.Quasithin.ChapterG.Section02.Binary.Recognition.Action

/-!
# The two original conjugate images generate the binary star quotient

The given moving g has a nonidentity cubic image: a trivial star image
would centralize V and hence normalize V₁. The nontrivial two-group U*
has order two. In S₃, its involution and its conjugate by that cubic are
distinct transpositions and generate all six permutations. Lifting their
six words proves I*=LT/O₂(LT), with the original g unchanged.

Source: Aschbacher–Smith, G.2.3(2), printed p.333.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G] {D : Setup G}

private theorem six_words : ∀ c u : Equiv.Perm (Fin 3), c ^ 3 = 1 → c ≠ 1 →
    u ^ 2 = 1 → u ≠ 1 → ∀ s,
      s = 1 ∨ s = u ∨ s = c⁻¹ * u * c ∨ s = u * (c⁻¹ * u * c) ∨
      s = (c⁻¹ * u * c) * u ∨ s = u * (c⁻¹ * u * c) * u := by
  decide +kernel

theorem binary_star_I_eq_top (h : D.BaseHypothesis) (b : D.BinaryNaturalData)
    (hUT : D.U ≤ D.T) (g : G) (hgL : g ∈ D.L) (hgN : g ∉ D.G₁)
    (e : D.Star ≃* Equiv.Perm (Fin 3)) : D.star (D.I g) = ⊤ := by
  have hcentral := binary_LT_core_centralizes_V h b
  let gl : D.L := ⟨g, hgL⟩
  let c : Equiv.Perm (Fin 3) := e (D.binaryLStar gl).val
  have hLcard : Nat.card (D.star D.L) = 3 := by
    rw [Nat.card_congr b.quotientEquiv.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hc3 : c ^ 3 = 1 := by
    have he : (D.binaryLStar gl) ^ 3 = 1 := by
      simpa only [hLcard] using (pow_card_eq_one' (x := D.binaryLStar gl))
    exact (map_pow e _ _).symm.trans ((congrArg e (congrArg Subtype.val he)).trans e.map_one)
  have hcne : c ≠ 1 := by
    intro he
    have hgl : (D.binaryLStar gl).val = 1 := e.map_eq_one_iff.mp he
    have hcore : g ∈ D.LT.pCoreIn 2 :=
      ⟨⟨g, (show D.L ≤ D.LT from le_sup_left) hgL⟩,
        (QuotientGroup.eq_one_iff _).mp hgl, rfl⟩
    exact hgN (centralizer_le_normalizer (D.V₁ : Set G)
      ((centralizer_le h.point_le) (hcentral hcore)))
  obtain ⟨u, hune⟩ := ne_bot_iff_exists_ne_one.mp b.image_nontrivial
  let t := e u.val
  have ht2 : t ^ 2 = 1 := by
    have he : u ^ 2 = 1 := by
      simpa only [binary_star_U_card h b hUT e] using (pow_card_eq_one' (x := u))
    exact (map_pow e _ _).symm.trans ((congrArg e (congrArg Subtype.val he)).trans e.map_one)
  have htne : t ≠ 1 := by
    intro he
    exact hune (Subtype.ext (e.map_eq_one_iff.mp he))
  let J := (D.star (D.I g)).map e.toMonoidHom
  have htJ : t ∈ J := mem_map_of_mem e.toMonoidHom
    ((binary_star_mono (show D.U ≤ D.I g from le_sup_left)) u.property)
  have hvJ : c⁻¹ * t * c ∈ J := by
    obtain ⟨u0, hu0, heu⟩ := u.property
    have huI : g⁻¹ * (u0 : G) * g ∈ D.I g := by
      apply mem_sup_right
      refine mem_map.mpr ⟨u0, hu0, ?_⟩
      change g⁻¹ * (u0 : G) * g⁻¹⁻¹ = g⁻¹ * (u0 : G) * g
      rw [inv_inv]
    have hmem : (D.binaryLStar gl).val⁻¹ * u.val * (D.binaryLStar gl).val ∈ D.star (D.I g) := by
      refine mem_map.mpr ⟨(inclusion (show D.L ≤ D.LT from le_sup_left) gl)⁻¹ * u0 *
        inclusion (show D.L ≤ D.LT from le_sup_left) gl, huI, ?_⟩
      simp only [map_mul, map_inv, heu]
      rfl
    have hm := mem_map_of_mem e.toMonoidHom hmem
    simpa only [map_mul, map_inv, J, c, t, MulEquiv.coe_toMonoidHom] using hm
  have hJ : J = ⊤ := by
    apply top_unique
    intro s _
    rcases six_words c t hc3 hcne ht2 htne s with he | he | he | he | he | he
    · exact he ▸ J.one_mem
    · exact he ▸ htJ
    · exact he ▸ hvJ
    · exact he ▸ J.mul_mem htJ hvJ
    · exact he ▸ J.mul_mem hvJ htJ
    · exact he ▸ J.mul_mem (J.mul_mem htJ hvJ) htJ
  apply (map_injective (f := e.toMonoidHom) e.injective)
  rw [map_top_of_surjective _ e.surjective]
  exact hJ

end CFSG.Quasithin.ChapterG.Section02.Setup
