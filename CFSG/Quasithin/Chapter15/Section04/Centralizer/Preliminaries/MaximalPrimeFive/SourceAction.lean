module

public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Preliminaries.MaximalPrimeSource
public import Theory.GroupTheory.PCoreProduct
public import Theory.GroupTheory.ConjugateSpanKernel
public import Theory.GroupTheory.CentralizerModulo.ConjugateSpan
public import Theory.GroupTheory.ConjugateSpanCentralizer
public import Theory.GroupTheory.ReducedNormal.Defs
public import Theory.GroupAction.FixedGeneratorCentralizer
public import Theory.Representation.NormalElementaryQuotient
public import Stellmacher.OmegaOneCenterMap

/-!
# The original prime action in 15.4.3(4)

For H=XT, the H-normal closure of Ω₁Z(T) is the original X-conjugate span.
The characteristic-two overgroup puts this elementary subgroup in O₂(M)
and makes O₂(M) centralize it. The image of X in its actual centralizer
quotient is therefore a normal subgroup of the prescribed prime order.
Fixed generators identify its centralizer and the action kernel is a
two-group contained in the original Sylow subgroup.

Source: Aschbacher–Smith, printed p.1157, proof of 15.4.3(4).
-/

noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section04.MaximalPrimeFive
open MaximalPrimeSource
variable {G : Type*} [Group G]

/-- The original local group XT. -/
public abbrev sourceGroup (T X : Subgroup G) := X ⊔ T

/-- The source elementary group, as a literal normal closure inside XT. -/
@[expose] public def sourceModule (T X : Subgroup G) : Subgroup (sourceGroup T X) :=
  normalClosure ((Stellmacher.omegaOneCenterAmbient T).subgroupOf (sourceGroup T X) :
    Set (sourceGroup T X))

/-- The literal source normal closure is normal in XT. -/
public instance sourceModule_normal (T X : Subgroup G) : (sourceModule T X).Normal := by
  unfold sourceModule
  infer_instance

private theorem omega_le (T : Subgroup G) : Stellmacher.omegaOneCenterAmbient T ≤ T := by
  intro z hz
  exact ((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).1

private theorem sylow_centralizes_omega (T : Subgroup G) :
    T ≤ centralizer (Stellmacher.omegaOneCenterAmbient T : Set G) := by
  intro t ht z hz
  exact (((Stellmacher.mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 t ht).symm

private theorem sourceX_normal {T X : Subgroup G} (hX : X ∈ Xi T) :
    (X.subgroupOf (sourceGroup T X)).Normal :=
  (normal_subgroupOf_iff_le_normalizer (show X ≤ sourceGroup T X from le_sup_left)).mpr
    (sup_le X.le_normalizer hX.1)

private theorem source_supplements (T X : Subgroup G) :
    X.subgroupOf (sourceGroup T X) ⊔ T.subgroupOf (sourceGroup T X) = ⊤ := by
  rw [← subgroupOf_sup (show X ≤ sourceGroup T X from le_sup_left)
    (show T ≤ sourceGroup T X from le_sup_right), subgroupOf_self]

/-- The normal-closure coordinates retain the original V=⟨Z^X⟩ exactly. -/
public theorem sourceModule_map_eq_span {T X : Subgroup G} (hX : X ∈ Xi T) :
    (sourceModule T X).map (sourceGroup T X).subtype =
      conjugateSpanBy (Stellmacher.omegaOneCenterAmbient T) X := by
  let H := sourceGroup T X
  let Z := Stellmacher.omegaOneCenterAmbient T
  have hZH : Z ≤ H := (omega_le T).trans le_sup_right
  have he : (sourceModule T X).map H.subtype = conjugateSpanBy Z H := by
    rw [sourceModule, normalClosure_subgroupOf_eq_conjugateSpanBy Z H hZH,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZH)]
  rw [he]
  apply le_antisymm ?_ (conjugateSpanBy_mono le_rfl le_sup_left)
  apply (closure_le _).mpr
  rintro v ⟨g, hg, z, hz, rfl⟩
  let : (X.subgroupOf H).Normal := sourceX_normal hX
  have hm : (⟨g, hg⟩ : H) ∈ X.subgroupOf H ⊔ T.subgroupOf H := by
    rw [source_supplements]; exact mem_top _
  obtain ⟨x, hx, t, ht, hxt⟩ := mem_sup_of_normal_left.mp hm
  have heq : (x : G) * t = g := congrArg Subtype.val hxt
  have hfix : (t : G) * z * (t : G)⁻¹ = z := by
    have hc : z * (t : G) = (t : G) * z := sylow_centralizes_omega T ht z hz
    rw [← hc, mul_inv_cancel_right]
  apply Subgroup.subset_closure
  refine ⟨x, hx, z, hz, ?_⟩
  calc
    (x : G) * z * (x : G)⁻¹ = x * ((t : G) * z * (t : G)⁻¹) * (x : G)⁻¹ := by rw [hfix]
    _ = ((x : G) * t) * z * ((x : G) * t)⁻¹ := by group
    _ = g * z * g⁻¹ := by rw [heq]

/-- Characteristic two puts V in O₂(M), makes O₂(M) centralize V, and
proves elementary abelianness of the actual normal closure. -/
public theorem sourceModule_core_and_elementary (T : Sylow 2 G)
    {X M : Subgroup G} (hXM : sourceGroup (T : Subgroup G) X ≤ M)
    (hM : M ∈ Chapter1.He G) :
    (sourceModule (T : Subgroup G) X).map (sourceGroup (T : Subgroup G) X).subtype ≤ M.pCoreIn 2 ∧
    M.pCoreIn 2 ≤ centralizer
      ((sourceModule (T : Subgroup G) X).map (sourceGroup (T : Subgroup G) X).subtype : Set G) ∧
    IsElementaryAbelian 2 (sourceModule (T : Subgroup G) X) := by
  let H := sourceGroup (T : Subgroup G) X
  let Z := Stellmacher.omegaOneCenterAmbient (T : Subgroup G)
  let W := conjugateSpanBy Z H
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  have hZC : Z ≤ centralizer (M.pCoreIn 2 : Set G) :=
    le_centralizer_iff.mp (hQT.trans (sylow_centralizes_omega _))
  have hZQ : Z ≤ M.pCoreIn 2 := fun z hz =>
    hM ⟨hTM ((omega_le _) hz), hZC hz⟩
  have hHQ : H ≤ normalizer (M.pCoreIn 2 : Set G) := hXM.trans
    (M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  have hWQ : W ≤ M.pCoreIn 2 := conjugateSpanBy_le hZQ hHQ
  have hQW : M.pCoreIn 2 ≤ centralizer (W : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ Z H hHQ
      (hQT.trans (sylow_centralizes_omega _))
  have hZH : Z ≤ H := (omega_le _).trans le_sup_right
  have he : (sourceModule (T : Subgroup G) X).map H.subtype = W := by
    rw [sourceModule, normalClosure_subgroupOf_eq_conjugateSpanBy Z H hZH,
      map_subgroupOf_eq_of_le (conjugateSpanBy_le_self hZH)]
  refine ⟨he ▸ hWQ, he ▸ hQW, ?_⟩
  let : IsElementaryAbelian 2 Z := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  let : IsMulCommutative W := le_centralizer_iff_isMulCommutative.mp (hWQ.trans hQW)
  let : IsElementaryAbelian 2 W := conjugateSpanBy_elementary_of_commutative Z H
  rw [sourceModule, normalClosure_subgroupOf_eq_conjugateSpanBy Z H hZH]
  exact IsElementaryAbelian.subgroupOf (conjugateSpanBy_le_self hZH)

private theorem core_quotient_prime {T X : Subgroup G} (hX : X ∈ Xi T) :
    (Nat.card (X ⧸ pCore 2 X)).Prime := by
  rw [← index_eq_card]
  exact hX.2.2.2.1

private theorem sourceX_not_centralizes_module {T X : Subgroup G}
    (hne : ¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient T : Set G)) :
    ¬ X.subgroupOf (sourceGroup T X) ≤
      centralizer (sourceModule T X : Set (sourceGroup T X)) := by
  intro hh
  apply hne
  intro x hx z hz
  have hzH : z ∈ sourceGroup T X := ((omega_le T).trans le_sup_right) hz
  exact congrArg Subtype.val (hh (show (⟨x, (show X ≤ sourceGroup T X from le_sup_left) hx⟩ : sourceGroup T X) ∈ X.subgroupOf (sourceGroup T X) from hx) ⟨z, hzH⟩ (le_normalClosure hz))

variable [Finite G]

/-- The actual centralizer quotient retains the prime image of X, its
self-centralizer, and the original T image as a disjoint supplement. -/
public theorem source_prime_image (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G))
    (hXM : sourceGroup (T : Subgroup G) X ≤ M)
    (hcore : X.pCoreIn 2 ≤ M.pCoreIn 2) (hM : M ∈ Chapter1.He G)
    (hne : ¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let H := sourceGroup (T : Subgroup G) X
    let W := sourceModule (T : Subgroup G) X
    let q := QuotientGroup.mk' (centralizer (W : Set H))
    let P := (X.subgroupOf H).map q
    Nat.card P = (pCore 2 X).index ∧ P.Normal ∧
      centralizer (P : Set (H ⧸ centralizer (W : Set H))) = P ∧
      Disjoint P ((T : Subgroup G).subgroupOf H |>.map q) := by
  let H := sourceGroup (T : Subgroup G) X
  let W := sourceModule (T : Subgroup G) X
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let Y := X.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let P := Y.map q
  let : Y.Normal := sourceX_normal hX
  have hYC : ¬ Y ≤ C := sourceX_not_centralizes_module hne
  let f : X →* H ⧸ C := q.comp (inclusion (show X ≤ H from le_sup_left))
  have hrange : f.range = P := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x.val, hx⟩, rfl⟩
  have hk : f.ker = pCore 2 X := by
    apply le_antisymm
    · apply normal_le_pCore_of_pPerfect_prime_quotient hX.2.1 (core_quotient_prime hX)
      intro ht
      apply hYC
      intro x hx
      have hxk : (⟨x.val, hx⟩ : X) ∈ f.ker := ht ▸ mem_top _
      exact (QuotientGroup.eq_one_iff (N := C) x).mp hxk
    · intro x hx
      apply (QuotientGroup.eq_one_iff (N := C) _).mpr
      intro w hw
      apply Subtype.ext
      exact (sourceModule_core_and_elementary T hXM hM).2.1
        (hcore (mem_map_of_mem X.subtype hx)) w (mem_map_of_mem H.subtype hw)
  have hp : Nat.card P = (pCore 2 X).index := by
    rw [← hrange, ← index_ker, hk]
  let : Fact (pCore 2 X).index.Prime := ⟨hX.2.2.2.1⟩
  let : IsCyclic P := isCyclic_of_prime_card hp
  have hfix : S ≤ centralizer ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H : Set H) := by
    intro t ht z hz
    exact Subtype.ext (sylow_centralizes_omega (T : Subgroup G) ht z hz)
  obtain ⟨hC, hd⟩ := centralizer_and_disjoint_quotient_images_of_fixed_normal_closure
    Y S ((Stellmacher.omegaOneCenterAmbient (T : Subgroup G)).subgroupOf H)
    (source_supplements _ _) hfix (inferInstance : IsMulCommutative P)
  exact ⟨hp, Normal.map inferInstance q (QuotientGroup.mk'_surjective C), hC, hd⟩

/-- The literal action kernel is a two-group in the original Sylow subgroup;
therefore its two-core is precisely the relative centralizer in T. -/
public theorem source_kernel_identity (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G))
    (hXM : sourceGroup (T : Subgroup G) X ≤ M)
    (hcore : X.pCoreIn 2 ≤ M.pCoreIn 2) (hM : M ∈ Chapter1.He G)
    (hne : ¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let H := sourceGroup (T : Subgroup G) X
    let W := sourceModule (T : Subgroup G) X
    let C := centralizer (W : Set H)
    C ≤ (T : Subgroup G).subgroupOf H ∧
      (T : Subgroup G).subgroupOf H ⊓ C = C.pCoreIn 2 := by
  let H := sourceGroup (T : Subgroup G) X
  let W := sourceModule (T : Subgroup G) X
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let Y := X.subgroupOf H
  let S := (T : Subgroup G).subgroupOf H
  let : Y.Normal := sourceX_normal hX
  have hYC : ¬ Y ≤ C := sourceX_not_centralizes_module hne
  let f : X →* H ⧸ C := q.comp (inclusion (show X ≤ H from le_sup_left))
  have hk : f.ker ≤ pCore 2 X := by
    apply normal_le_pCore_of_pPerfect_prime_quotient hX.2.1 (core_quotient_prime hX)
    intro ht
    apply hYC
    intro x hx
    have hxk : (⟨x.val, hx⟩ : X) ∈ f.ker := ht ▸ mem_top _
    exact (QuotientGroup.eq_one_iff (N := C) x).mp hxk
  have hTM : (T : Subgroup G) ≤ M := le_sup_right.trans hXM
  have hQT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTM] using
      pCoreIn_le_sylow M (T.subtype hTM)
  have hd := (source_prime_image T hX hXM hcore hM hne).2.2.2
  have hCS : C ≤ S := by
    intro c hc
    obtain ⟨y, hy, s, hs, he⟩ := mem_sup_of_normal_left.mp
      (show c ∈ Y ⊔ S by rw [source_supplements]; exact mem_top c)
    have hprod : q y * q s = 1 := by
      rw [← map_mul, he]
      exact (QuotientGroup.eq_one_iff (N := C) c).mpr hc
    have hyS : q y ∈ S.map q := by
      have heq : q y = (q s)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      rw [heq]
      exact (S.map q).inv_mem (mem_map_of_mem q hs)
    have hy1 : q y = 1 := mem_bot.mp
      ((disjoint_iff.mp hd) ▸ (show q y ∈ Y.map q ⊓ S.map q from
        ⟨mem_map_of_mem q hy, hyS⟩))
    have hycore : (⟨y.val, hy⟩ : X) ∈ pCore 2 X := hk hy1
    have hyT : y ∈ S := hQT (hcore (mem_map_of_mem X.subtype hycore))
    rw [← he]
    exact S.mul_mem hyT hs
  have hS : IsPGroup 2 S := T.isPGroup'.comap_subtype
  have hC : IsPGroup 2 C := hS.to_le hCS
  exact ⟨hCS, by rw [inf_eq_right.mpr hCS, pCoreIn_eq_self_of_isPGroup 2 C hC]⟩

/-- The actual prime image has a trivial two-core, so the original elementary
normal closure belongs to R₂(XT). Reducedness is proved, not assumed. -/
public theorem sourceModule_reduced (T : Sylow 2 G) {X M : Subgroup G}
    (hX : X ∈ Xi (T : Subgroup G))
    (hXM : sourceGroup (T : Subgroup G) X ≤ M)
    (hcore : X.pCoreIn 2 ≤ M.pCoreIn 2) (hM : M ∈ Chapter1.He G)
    (hne : ¬ X ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    IsPReduced 2 (sourceModule (T : Subgroup G) X) := by
  let H := sourceGroup (T : Subgroup G) X
  let W := sourceModule (T : Subgroup G) X
  let C := centralizer (W : Set H)
  let q := QuotientGroup.mk' C
  let P := (X.subgroupOf H).map q
  let p := (pCore 2 X).index
  have hp : p.Prime := hX.2.2.2.1
  have hpodd : Odd p := hX.2.2.2.2
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨hP, hnP, hCP, _⟩ := source_prime_image T hX hXM hcore hM hne
  let : P.Normal := hnP
  have hPcard : Nat.card P = p := hP
  have hCPeq : centralizer (P : Set (H ⧸ C)) = P := hCP
  have hPg : IsPGroup p P := IsPGroup.of_card (n := 1) (by simpa only [pow_one] using hPcard)
  have hd : Disjoint (pCore 2 (H ⧸ C)) P :=
    IsPGroup.disjoint_of_coprime pCore_isPGroup hPg hpodd.coprime_two_left
  refine ⟨inferInstance, (sourceModule_core_and_elementary T hXM hM).2.2, ?_⟩
  have hle : pCore 2 (H ⧸ C) ≤ P := by
    rw [← hCPeq]
    exact commutator_eq_bot_iff_le_centralizer.mp (commutator_eq_bot_of_disjoint hd)
  exact bot_unique (fun x hx => (disjoint_iff.mp hd) ▸ (show x ∈ pCore 2 (H ⧸ C) ⊓ P from ⟨hx, hle hx⟩))

end CFSG.Quasithin.Chapter15.Section04.MaximalPrimeFive
