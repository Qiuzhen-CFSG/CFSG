module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension.Preparation


/-!
# The source omega-center module and the full reduced core

The normal closure of the Sylow omega-center is independent of the chosen
Sylow subgroup, hence characteristic. This is the module in B.2.16, which
must be distinguished from the full `R₂`. In a three-prime group the
exceptional alternative contains an actual `L₂(2)` section and is impossible.
If the module centralizer is a two-group, Thompson heredity makes `J(S)`
normal in the whole group. Thus the literal factorization through `R₂`
follows without identifying `R₂` with the smaller omega-center module.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
B.2.14–16, printed pp.78–79, and 15.3.68, printed pp.1154–1155.
-/

public section

open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension
open Chapter1.RadicalNormalizers.ThompsonSource
variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem closure_map (S : Sylow 2 H) (e : MulAut H) :
    closure (e • S) = (closure S).map e.toMonoidHom := by
  change normalClosure (omegaOneCenterAmbient ((S : Subgroup H).map e.toMonoidHom) : Set H) = _
  rw [omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective,
    coe_map, ← map_normalClosure _ _ e.surjective]
  rfl

theorem closure_eq (S T : Sylow 2 H) : closure S = closure T := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H S T
  change closure S = closure ((MulAut.conj g) • S)
  rw [closure_map]
  exact (Normal.map_conj_eq (closure S) g).symm

theorem closure_characteristic (S : Sylow 2 H) : (closure S).Characteristic := by
  rw [characteristic_iff_map_eq]
  intro e
  rw [← closure_map]
  exact closure_eq _ _

theorem omegaCenter_le_thompson (S : Subgroup H) :
    omegaOneCenterAmbient S ≤ elementaryAbelianMaxJ S := by
  let : IsElementaryAbelian 2 (omegaOneCenterAmbient S) :=
    omegaOneCenterAmbient_elementaryAbelian S
  have hES : omegaOneCenterAmbient S ≤ S := fun x hx =>
    ((mem_omegaOneCenterAmbient_iff S x).mp hx).1
  have hEC : omegaOneCenterAmbient S ≤ centralizer (elementaryAbelianMaxJ S : Set H) := by
    intro x hx
    exact mem_centralizer_iff.mpr fun j hj =>
      ((mem_omegaOneCenterAmbient_iff S x).mp hx).2.2 j
        ((show elementaryAbelianMaxJ S ≤ S from sSup_le fun _ hA => hA.1) hj)
  intro x hx
  exact ((mem_omegaOneCenterAmbient_iff _ x).mp
    (elementary_centralizer_maxJ_le_omegaCenter S _ hES hEC hx)).1

theorem omegaCenter_le_sylowImage (U : Sylow 2 H) :
    omegaOneCenterAmbient (U : Subgroup H) ≤ omegaOneCenterAmbient (sylowImage U) := by
  intro x hx
  obtain ⟨_, hp, hc⟩ := (mem_omegaOneCenterAmbient_iff _ x).mp hx
  exact (mem_omegaOneCenterAmbient_iff _ x).mpr
    ⟨mem_sup_right (omegaCenter_le_thompson _ hx), hp,
      fun q hq => hc q (sylowImage_le U hq)⟩

theorem centralizes_closure_of_three_coprime {S : Sylow 2 H}
    (h : Conclusion S) (h3 : Nat.Coprime 3 (Nat.card H)) :
    elementaryAbelianMaxJ (S : Subgroup H) ≤ centralizer (closure S : Set H) := by
  let := h.elementary
  have halt := h.alternatives
  cases halt with
  | inl hf => exact hf.1
  | inr he =>
    obtain ⟨d⟩ := he
    exact ((Nat.prime_three.coprime_iff_not_dvd.mp h3) d.three_dvd_card).elim

theorem thompson_normal_of_centralizer_two {S : Sylow 2 H}
    (hJ : elementaryAbelianMaxJ (S : Subgroup H) ≤ centralizer (closure S : Set H))
    (hC : IsPGroup 2 (centralizer (closure S : Set H))) :
    (elementaryAbelianMaxJ (S : Subgroup H)).Normal := by
  have he := thompson_intermediate (S : Subgroup H) (centralizer (closure S : Set H))
    hJ (hC.le_sylow_of_normal S)
  rw [← he, normal_iff_map_conj_eq]
  intro g
  change (elementaryAbelianMaxJ _).map (MulAut.conj g).toMonoidHom = _
  rw [← elementaryAbelianMaxJ_map_equiv]
  congr 1
  exact Normal.map_conj_eq _ g

omit [Finite H] in
theorem normalizes_image (X : Subgroup H) (D : Subgroup X) [D.Normal] :
    X ≤ normalizer (D.map X.subtype : Set H) := by
  intro x hx
  apply D.le_normalizer_map X.subtype
  apply mem_map.mpr
  refine ⟨⟨x, hx⟩, ?_, rfl⟩
  rw [normalizer_eq_top]
  trivial

omit [Finite H] in
theorem product_of_normalizes (X J Z₀ : Subgroup H)
    (h : X ≤ normalizer (J : Set H)) :
    (X : Set H) = (X ⊓ centralizer (Z₀ : Set H) : Set H) *
      (X ⊓ normalizer (J : Set H) : Set H) := by
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨1, ⟨X.one_mem, (centralizer (Z₀ : Set H)).one_mem⟩,
      x, ⟨hx, h hx⟩, one_mul x⟩
  · rintro x ⟨a, ha, b, hb, rfl⟩
    exact X.mul_mem ha.1 hb.1

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.ThompsonExtension
