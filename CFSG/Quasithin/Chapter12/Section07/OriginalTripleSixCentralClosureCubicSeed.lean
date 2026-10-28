module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarFrattini
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixCentralClosureScalarFixedModule

/-!
# The literal source cubic-normalizer seed

For the actual scalar cubic Y the source subgroup
Z_Y=Ω₁Z(N_T(Y))∩O₂(KT) is exactly C_{O₂(KT)}(X)∩Ω₁Z(T).
The equality follows from the proved T=U N_T(Y), the full two-core's
centralization of U, and coprimality. Thus the preceding reduced module
is generated from the literal source seed, with all core kernels retained.

Source: Aschbacher--Smith12.7.20, printed p.846.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterE ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

/-- Identify the literal cubic-normalizer seed and construct its original
K-span as the secondary reduced module, with its quadratic W-action. -/
theorem original_tripleSix_central_closure_cubic_seed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T K)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T K U) (a : ActionEquiv D.quotientAction Hexacode.evenAction)
    (z : U) (hz : z ≠ 1)
    (hzT : (T : Subgroup G) ≤ centralizer ({(z : G)} : Set G))
    (hnot : ¬ U ≤ (centralizer ({(z : G)} : Set G)).pCoreIn 2)
    (houter : ¬ inducedAutomizer U (conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))) ≤ inducedAutomizer U K) :
    let M := K ⊔ (T : Subgroup G)
    let X := tripleSixScalarResidual K
    let Q := M.pCoreIn 2
    let W := conjugateSpanBy (tripleSixPoint D a z)
      (conjugateSpanBy U (centralizer ({(z : G)} : Set G)))
    ∃ Y : Subgroup G, Y ≤ X ∧ Nat.card Y = 3 ∧ X = U ⊔ Y ∧
      (let ZY := omegaCenterIn ((T : Subgroup G) ⊓ normalizer (Y : Set G)) ⊓ Q
       let VY := conjugateSpanBy ZY K
       ZY = (Q ⊓ centralizer (X : Set G)) ⊓ omegaCenterIn (T : Subgroup G) ∧
       ZY ≤ omegaCenterIn (T : Subgroup G) ∧
       (Q ≠ U → ZY ≠ ⊥ ∧ VY ≠ ⊥) ∧
       VY ≤ Q ⊓ centralizer (Y : Set G) ∧
       IsPReduced 2 (VY.subgroupOf M) ∧
       IsPReduced 2 ((U ⊔ VY).subgroupOf M) ∧
       Disjoint U VY ∧ ⁅⁅VY,W⁆,W⁆ = ⊥) := by
  let M := K ⊔ (T : Subgroup G)
  let X := tripleSixScalarResidual K
  let Q := M.pCoreIn 2
  let C := Q ⊓ centralizer (X : Set G)
  let Z := C ⊓ omegaCenterIn (T : Subgroup G)
  let V := conjugateSpanBy Z K
  obtain ⟨Y,hYX,hYcard,hXY,_,hT,_⟩ :=
    original_tripleSix_central_closure_scalar_frattini h structural D a z hz hzT hnot houter
  change Y ≤ X at hYX
  change X=U ⊔ Y at hXY
  let NT := (T : Subgroup G) ⊓ normalizer (Y : Set G)
  change (T : Subgroup G)=U ⊔ NT at hT
  have hQT : Q ≤ (T : Subgroup G) := by
    have hh := pCoreIn_le_sylow M (T.subtype (show (T : Subgroup G) ≤ M from le_sup_right))
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ M from le_sup_right)] at hh
  have hXQ : X ≤ normalizer (Q : Set G) :=
    ((map_subtype_le _).trans (show K ≤ M from le_sup_left)).trans
      (M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hY2 : IsPGroup 3 Y := IsPGroup.of_card (p:=3) (n:=1) (by simpa using hYcard)
  have hd : Disjoint Q Y := IsPGroup.disjoint_of_ne 2 3 (by decide) Q Y
    (isPGroup_pCoreIn 2 M) hY2
  have hfix : Q ⊓ centralizer (Y : Set G)=C := by
    apply le_antisymm
    · refine le_inf inf_le_left ?_
      apply le_centralizer_iff.mp
      rw [hXY]
      exact sup_le ((le_centralizer_iff.mp D.core_centralizes).trans
        (centralizer_le inf_le_left)) (le_centralizer_iff.mp inf_le_right)
    · exact inf_le_inf_left _ (centralizer_le hYX)
  have hNC : Q ⊓ normalizer (Y : Set G)=C :=
    (SylowThreeNormalizer.normalizer_inf_eq_centralizer_inf Q Y (hYX.trans hXQ) hd).trans hfix
  have he : omegaCenterIn NT ⊓ Q=Z := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxNT,hxc,hxs⟩ := (mem_omegaCenterIn_iff NT x).mp hx.1
      have hxC : x ∈ C := hNC ▸ (show x ∈ Q ⊓ normalizer (Y : Set G) from ⟨hx.2,hxNT.2⟩)
      have hxT : x ∈ centralizer (T : Set G) := by
        apply mem_centralizer_iff.mpr
        have hTC : (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
          rw [hT]
          exact sup_le
            (fun u hu => mem_centralizer_singleton_iff.mpr (D.core_centralizes hx.2 u hu))
            (fun n hn => mem_centralizer_singleton_iff.mpr (hxc n hn))
        intro t ht
        exact mem_centralizer_singleton_iff.mp (hTC ht)
      exact ⟨hxC,(mem_omegaCenterIn_iff T x).mpr ⟨hxNT.1,hxT,hxs⟩⟩
    · intro x hx
      obtain ⟨hxT,hxc,hxs⟩ := (mem_omegaCenterIn_iff T x).mp hx.2
      have hxY : x ∈ centralizer (Y : Set G) := centralizer_le hYX hx.1.2
      exact ⟨(mem_omegaCenterIn_iff NT x).mpr
        ⟨⟨hxT,Subgroup.centralizer_le_normalizer _ hxY⟩,centralizer_le inf_le_left hxc,hxs⟩,hx.1.1⟩
  have hf := original_tripleSix_central_closure_scalar_fixed_module
    h structural D a z hz hzT hnot houter
  change M ≤ normalizer (C : Set G) ∧
    (Q ≠ U → Z ≠ ⊥ ∧ V ≠ ⊥) ∧ V ≤ C ∧
    V = conjugateSpanBy Z M ∧ IsPReduced 2 (V.subgroupOf M) ∧
    IsPReduced 2 ((U ⊔ V).subgroupOf M) ∧ Disjoint U V ∧ _ at hf
  refine ⟨Y,hYX,hYcard,hXY,?_⟩
  change omegaCenterIn NT ⊓ Q=Z ∧ _
  rw [he]
  exact ⟨rfl,inf_le_right,hf.2.1,hf.2.2.1.trans hfix.symm.le,
    hf.2.2.2.2.1,hf.2.2.2.2.2.1,hf.2.2.2.2.2.2.1,hf.2.2.2.2.2.2.2⟩

end CFSG.Quasithin.Chapter12.Section07
