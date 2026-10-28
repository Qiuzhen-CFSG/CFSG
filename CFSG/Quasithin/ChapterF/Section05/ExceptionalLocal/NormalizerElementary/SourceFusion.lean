module
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerElementary.Family
public import CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal.NormalizerQuotientCard

/-!
# Root transitivity and the point normalizer quotient from source hypotheses

The literal four-member elementary family discharges the local premises of
Burnside fusion and normalizer incidence. Thus each normalizer is transitive
on its roots. For A₁, T of order128 and E₁ of order96 both lie in the point
stabilizer, so384 divides its order. The faithful five-root action gives
the opposite bound via orbit-stabilizer. Equality identifies N_G(A₁)/A₁
with S₅ without an additional finite point-stabilizer calculation.

Source: Aschbacher–Smith F.5.4(4), printed p.301. `FusionFacts` is the
independently proved earlier-source input, retained for final assembly.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
local notation "hn" => Nat.le_refl 1
variable {G G0 : Type*} [Group G] [Group G0] [Finite G]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G) (z : pointParabolic 1 hn) (h : Source.Hypotheses c i z)
  (t : G) (hf : FusionFacts c i z t)
local notation "T" => Source.sylowImage c i

omit [Finite G] in
include h hf in
/-- The original Sylow contains an element moving the marked short involution. -/
theorem normalizer_exists_outside_Tcentralizer : ∃ y∈T, y∉Tcentralizer c i t := by
  obtain ⟨y,hy,he⟩ := hf.t_fuses_t_root
  refine ⟨y,hy,?_⟩
  intro hyt
  have hc := mem_centralizer_singleton_iff.mp hyt.2
  have hfix : y*t*y⁻¹=t := by rw [hc,mul_inv_cancel_right]
  have hz : rootElement c i z=1 := mul_left_cancel (he.symm.trans hfix |>.trans (mul_one t).symm)
  have ho := source_root_order c i z h
  rw [hz,orderOf_one] at ho
  omega

include h hf in
/-- The source normalizer action is transitive on the roots in each Aᵢ;
the literal family and both normal members are discharged here. -/
theorem normalizer_root_transitive (b : Bool) :
    ∀ x∈A c i b, IsConj (rootElement c i z) x →
      ∃ n∈normalizer (A c i b : Set G), MulAut.conj n (rootElement c i z)=x := by
  obtain ⟨y,hy,hyt⟩ := normalizer_exists_outside_Tcentralizer c i z h t hf
  exact normalizer_root_transitive_of_family c i z t hf y hy
    (normalizer_T_normalizes_A_point c i z h t hf y hy hyt)
    (normalizer_T_normalizes_Q c i z h) (normalizer_point_A_ne_Q c i z t hf)
    (normalizer_elementary_normal_cases c i z h t hf y hy hyt)
    (fun B hBT he hc => (normalizer_elementary_list c i z h t hf y hy hyt B).mp ⟨hBT,he,hc⟩) b

include h hf in
/-- The two original normal elementary cores are not ambient conjugate. -/
theorem normalizer_point_not_conjugate_Q_of_source :
    ∀ g : G, (A c i false).conjBy g ≠ Q c i true := by
  obtain ⟨y,hy,hyt⟩ := normalizer_exists_outside_Tcentralizer c i z h t hf
  exact normalizer_point_not_conjugate_Q c i z t hf
    (normalizer_T_normalizes_A_point c i z h t hf y hy hyt)
    (normalizer_T_normalizes_Q c i z h) (normalizer_point_A_ne_Q c i z t hf)
    (normalizer_elementary_normal_cases c i z h t hf y hy hyt)

include h hf in
/-- The point endpoint stabilizer has order384. Its subgroups T and E₁ force
the lower bound, while the faithful five-root action forces the upper bound. -/
theorem normalizer_point_stabilizer_card :
    Nat.card (M c i false ⊓ normalizer (A c i false : Set G) : Subgroup G)=384 := by
  obtain ⟨y,hy,hyt⟩ := normalizer_exists_outside_Tcentralizer c i z h t hf
  have hT : T≤M c i false ⊓ normalizer (A c i false : Set G) :=
    le_inf (sylowImage_le_M c i false)
      (normalizer_T_normalizes_A_point c i z h t hf y hy hyt)
  have hE : E c i false≤M c i false ⊓ normalizer (A c i false : Set G) :=
    le_inf inf_le_left (E_le_normalizer_A c i false)
  have hdT := card_dvd_of_le hT
  rw [hf.sylow_card] at hdT
  have hdE := card_dvd_of_le hE
  obtain ⟨e⟩ := hf.E_iso false
  rw [Nat.card_congr e.toEquiv] at hdE
  norm_num [Nat.card_prod,Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] at hdE
  have h384 := Nat.lcm_dvd hdT hdE
  norm_num at h384
  have hlo := Nat.le_of_dvd (Nat.card_pos (α := ↥(M c i false ⊓
    normalizer (A c i false : Set G)))) h384
  have hq := Nat.le_of_dvd (by decide : 0<120) (pointNormalizer_card_dvd c i z t hf h)
  have hmul := normalizer_quotient_card_of_root_transitive c i z t hf false
    (normalizer_root_transitive c i z h t hf false)
  rw [hf.root_class_A_point] at hmul
  omega

include h hf in
/-- The actual first normalizer quotient is S₅ with no remaining local
stabilizer or transitivity premise. -/
theorem normalizer_point_quotient_of_source :
    Nonempty (normalizerQuotient c i false ≃* Equiv.Perm (Fin 5)) :=
  normalizer_point_quotient_of_transitive c i z t hf h
    (normalizer_root_transitive c i z h t hf false)
    (normalizer_point_stabilizer_card c i z h t hf)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
