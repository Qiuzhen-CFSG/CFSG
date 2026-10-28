module

public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FirstQuotient
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.SecondQuotient

/-!
# Source local factors and compatible Tits--Ree core quotients

For these concrete marked parabolics choose the source local factors to be the
embedded prime-to-two residuals O^{2′}(Pᵢ). Each equals Pᵢ: the marked Sylow group
and the adjoined reflection consist of two-elements and generate Pᵢ. Their joins
with S and with the whole overlap are therefore the specified full parabolics.
Normality is stated inside each parabolic, not inside the simple ambient group.

The two quotient maps induced by the canonical Atlas embedding are bijective
and commute with the actual Sz(2) and PSL₂(2) projections. This identifies the
local quotients in the Tits subgroup and its full Ree extension with exactly the
same matrix carriers and quotient conventions.

The first Tits core has order 512 and quotient Sz(2), of order 20; the second
has core order 1024 and quotient PSL₂(2). The incompatible 1024/D₁₀ pair printed
in F.1.12(I)(9) is separately excluded for every subgroup of the first parabolic
in `SourceCorrection`. Changing L₁ to a proper subgroup cannot repair that pair.

Source: Aschbacher--Smith F.1.11--12, printed pp.262--264, and 14.2.20--21,
printed pp.988--989; Parrott (1972), pp.672, 683.
-/

@[expose] public section
noncomputable section
namespace Tits.ExceptionalParabolics
open Subgroup Theory.GroupTheory

/-- The chosen source L₁, before identifying it with its full parabolic. -/
def firstLocalFactor : Subgroup Atlas1600Group :=
  (primeToResidual 2 first).map first.subtype

/-- The chosen source L₂, before identifying it with its full parabolic. -/
def secondLocalFactor : Subgroup Atlas1600Group :=
  (primeToResidual 2 second).map second.subtype

private theorem residual_map_eq (P : Subgroup Atlas1600Group) (r : Atlas1600Group)
    (hr : r ^ 2 = 1) (hP : S ⊔ closure {r} = P) :
    (primeToResidual 2 P).map P.subtype = P := by
  apply le_antisymm
  · rintro _ ⟨x, _, rfl⟩
    exact x.property
  · have hS : S ≤ P := hP ▸ le_sup_left
    have hgen : r ∈ P := hP ▸ (show closure {r} ≤ S ⊔ closure {r} from le_sup_right)
      (subset_closure (Set.mem_singleton r))
    apply le_trans (le_of_eq hP.symm)
    apply sup_le
    · intro x hx
      have htwo : IsPGroup 2 S := IsPGroup.of_card (n := 11) (by simpa using sylow_card)
      obtain ⟨n, hn⟩ := htwo ⟨x, hx⟩
      exact ⟨⟨x, hS hx⟩, mem_primeToResidual_of_pow
        (n := n) (Subtype.ext (congrArg (fun a : S => (a : Atlas1600Group)) hn)), rfl⟩
    · apply (closure_le _).mpr
      intro x hx
      have hx' : x = r := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨r, hgen⟩, mem_primeToResidual_of_pow (n := 1) (Subtype.ext hr), rfl⟩

theorem firstLocalFactor_eq : firstLocalFactor = first :=
  residual_map_eq first (atlas1600ParrottAssignment .r1)
    (by simpa [parrottRelator] using atlas1600ParrottAssignment_relations .i_r1) rfl

theorem secondLocalFactor_eq : secondLocalFactor = second :=
  residual_map_eq second (atlas1600ParrottAssignment .r8)
    (by simpa [parrottRelator] using atlas1600ParrottAssignment_relations .i_r8) rfl

theorem firstLocalFactor_sup_sylow : firstLocalFactor ⊔ S = first := by
  rw [firstLocalFactor_eq, sup_eq_left.mpr sylow_le_first]

theorem secondLocalFactor_sup_sylow : secondLocalFactor ⊔ S = second := by
  rw [secondLocalFactor_eq, sup_eq_left.mpr sylow_le_second]

theorem localFactor_core_cards :
    Nat.card (pCore 2 firstLocalFactor) = 512 ∧
      Nat.card (pCore 2 secondLocalFactor) = 1024 := by
  rw [firstLocalFactor_eq, secondLocalFactor_eq]
  exact ⟨FirstQuotient.core_card, second_core_card⟩

instance firstLocalFactor_normal : (firstLocalFactor.subgroupOf first).Normal := by
  rw [firstLocalFactor_eq, Subgroup.subgroupOf_self]
  infer_instance

instance secondLocalFactor_normal : (secondLocalFactor.subgroupOf second).Normal := by
  rw [secondLocalFactor_eq, Subgroup.subgroupOf_self]
  infer_instance

theorem firstLocalFactor_sup_overlap : firstLocalFactor ⊔ overlap = first := by
  rw [overlap_eq_sylow, firstLocalFactor_sup_sylow]

theorem secondLocalFactor_sup_overlap : secondLocalFactor ⊔ overlap = second := by
  rw [overlap_eq_sylow, secondLocalFactor_sup_sylow]

def firstLocalFactorCoreQuotientEquiv : (firstLocalFactor ⧸ pCore 2 firstLocalFactor) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  (LocalCoreTransport.quotientEquiv 2 (MulEquiv.subgroupCongr firstLocalFactor_eq)).trans
    FirstQuotient.coreQuotientEquiv

def secondLocalFactorCoreQuotientEquiv : (secondLocalFactor ⧸ pCore 2 secondLocalFactor) ≃*
    ReeF4.LargeLocalSeeds.LinearQuotient 0 :=
  (LocalCoreTransport.quotientEquiv 2 (MulEquiv.subgroupCongr secondLocalFactor_eq)).trans
    secondCoreQuotientEquiv

/-- The literal quotient map induced by the restricted Atlas embedding. -/
def firstQuotientToFull : (first ⧸ pCore 2 first) →*
    (FullRee.first ⧸ pCore 2 FullRee.first) :=
  QuotientGroup.map _ _ FirstQuotient.embedding
    (by rw [FirstQuotient.core_eq_comap])

@[simp] theorem firstQuotientToFull_mk (x : first) :
    firstQuotientToFull (QuotientGroup.mk' (pCore 2 first) x) =
      QuotientGroup.mk' (pCore 2 FullRee.first) (FirstQuotient.embedding x) := rfl

theorem firstQuotientToFull_compatible (x : first ⧸ pCore 2 first) :
    FullRee.firstCoreQuotientEquiv (firstQuotientToFull x) =
      FirstQuotient.coreQuotientEquiv x := by
  refine QuotientGroup.induction_on x ?_
  intro x
  rfl

theorem second_core_eq_comap :
    pCore 2 second = (pCore 2 FullRee.second).comap secondEmbedding := by
  rw [← secondProjection_ker, ← FullRee.secondProjection_ker]
  rfl

/-- The analogous literal map on the linear-side quotients. -/
def secondQuotientToFull : (second ⧸ pCore 2 second) →*
    (FullRee.second ⧸ pCore 2 FullRee.second) :=
  QuotientGroup.map _ _ secondEmbedding (by rw [second_core_eq_comap])

@[simp] theorem secondQuotientToFull_mk (x : second) :
    secondQuotientToFull (QuotientGroup.mk' (pCore 2 second) x) =
      QuotientGroup.mk' (pCore 2 FullRee.second) (secondEmbedding x) := rfl

theorem secondQuotientToFull_compatible (x : second ⧸ pCore 2 second) :
    FullRee.secondCoreQuotientEquiv (secondQuotientToFull x) =
      secondCoreQuotientEquiv x := by
  refine QuotientGroup.induction_on x ?_
  intro x
  rfl


theorem firstQuotientToFull_bijective : Function.Bijective firstQuotientToFull := by
  have h : ⇑firstQuotientToFull =
      FullRee.firstCoreQuotientEquiv.symm ∘ FirstQuotient.coreQuotientEquiv := by
    funext x
    apply FullRee.firstCoreQuotientEquiv.injective
    rw [Function.comp_apply, MulEquiv.apply_symm_apply, firstQuotientToFull_compatible]
  rw [h]
  exact FullRee.firstCoreQuotientEquiv.symm.bijective.comp
    FirstQuotient.coreQuotientEquiv.bijective

theorem secondQuotientToFull_bijective : Function.Bijective secondQuotientToFull := by
  have h : ⇑secondQuotientToFull =
      FullRee.secondCoreQuotientEquiv.symm ∘ secondCoreQuotientEquiv := by
    funext x
    apply FullRee.secondCoreQuotientEquiv.injective
    rw [Function.comp_apply, MulEquiv.apply_symm_apply, secondQuotientToFull_compatible]
  rw [h]
  exact FullRee.secondCoreQuotientEquiv.symm.bijective.comp secondCoreQuotientEquiv.bijective

end Tits.ExceptionalParabolics
