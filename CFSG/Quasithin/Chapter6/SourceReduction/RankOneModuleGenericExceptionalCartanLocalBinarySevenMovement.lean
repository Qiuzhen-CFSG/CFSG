module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryCoreContainment
public import Theory.GroupTheory.CoprimeCentralizerDecomposition

/-!
# The original seven-group moves the intersection of the two cores

Let X = CT, U = ⟨Ω₁Z(T)ᴸ⟩, E = U intersect O₂(X), and N = ⟨Eˣ⟩.
The component action on N/Φ(N) has a two-group kernel. The original right
Hall subgroup B lies in the component and has order seven, so restricting
that SAME action to B is faithful. Its fixation of U does not extend to N.

Consequently P = [N,B] survives in N/Φ(N). The earlier mutual-action
calculation makes P centralize U; the actual reduced omega-span identifies
C_T(U) with O₂(LT), placing P in O₂(X) intersect O₂(LT). Coprime action
gives N = P C_N(B), and B moves P, so P is not contained in U.
All actions and Frattini maps are literal conjugation maps. The original
E, full module W and both Hall conditions are retained.

This locates a nontrivial seven-moved subgroup in the intersection of the
original cores. Excluding the remaining large-span configuration and
constructing the exceptional component witness are still required for
SourceLocalCartanEscape; no core-free Sylow model is inferred.

Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638, and the
seven-centralizer argument in 5.2.2, printed p.648, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

/-- The original right Hall seven-group acts faithfully on the retained
span's Frattini quotient, with its conjugation action explicitly identified. -/
theorem original_binary_triality_seven_frattini_action
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    ∃ a : B →* MulAut N,
      (∀ (b : B) (v : N), ((a b v : N) : G) =
        (b : G) * (v : G) * (b : G)⁻¹) ∧
      Function.Injective ((quotientAut (frattini N)).comp a) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨a,ha,hker,_,_⟩ := original_binary_triality_kernel_frattini_image
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hKR,_,_⟩ := LocalSieve.binaryTriality_residual_section h.qtke hKH
    hH.1.1.2 hK hKT horbit hY hescape C hC hKC hm
  have hBC : B ≤ C.map Y.subtype :=
    (Global.right_cartan_le_residual c).trans (hKR ▸ hKC)
  let e := C.equivMapOfInjective Y.subtype Y.subtype_injective
  let i : B →* C := e.symm.toMonoidHom.comp (inclusion hBC)
  have hi : Function.Injective i := e.symm.injective.comp (inclusion_injective hBC)
  let b := a.comp i
  let d := (quotientAut (frattini N)).comp b
  have hb := (original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.2.2.2.1
  have hk : d.ker ≤ (pCore 2 C).comap i := by
    intro x hx
    exact hker hx
  have hkp : IsPGroup 2 d.ker :=
    (pCore_isPGroup.comap_of_injective i hi).to_le hk
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hB : IsPGroup 7 B := IsPGroup.of_card (n := 1) (by simpa using hb)
  have hzero : d.ker = ⊥ := disjoint_self.mp
    (IsPGroup.disjoint_of_ne 2 7 (by decide) d.ker d.ker hkp (hB.to_subgroup d.ker))
  refine ⟨b,?_,(MonoidHom.ker_eq_bot_iff d).mp hzero⟩
  intro x v
  have hix : ((i x).val : G) = (x : G) :=
    congrArg Subtype.val (e.apply_symm_apply (inclusion hBC x))
  simpa only [b,MonoidHom.comp_apply,hix] using ha (i x) v

/-- The seven-moved subgroup lies in both original cores and centralizes U.
It survives modulo the retained Frattini subgroup and escapes U; the
original seven-action gives the coprime decomposition of N. -/
theorem original_binary_triality_seven_moved_core
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    let X := C.map Y.subtype ⊔ (T : Subgroup G)
    let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
    let E := U ⊓ X.pCoreIn 2
    let N := conjugateSpanBy E X
    let P := ⁅N,B⁆
    P ≤ X.pCoreIn 2 ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      P ≤ centralizer (U : Set G) ∧
      ¬ P ≤ (frattini N).map N.subtype ∧
      ¬ P ≤ centralizer (B : Set G) ∧ ¬ P ≤ U ∧
      N = P ⊔ (N ⊓ centralizer (B : Set G)) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  let P := ⁅N,B⁆
  obtain ⟨hu,_,hb,hBU,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hNQ,hXN,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hHX : H ≤ X := by
    rw [←hKT]
    exact sup_le (hKC.trans le_sup_left) le_sup_right
  have hBN : B ≤ normalizer (N : Set G) :=
    (c.right_le.trans inf_le_right).trans (hHX.trans hXN)
  have hPN : P ≤ N := le_normalizer_iff_commutator_le_left.mp hBN
  have hPU : P ≤ centralizer (U : Set G) :=
    (original_binary_triality_kernel_mutual_action
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2.2.2.2
  have hQT : X.pCoreIn 2 ≤ (T : Subgroup G) :=
    (pCoreIn_le_sylow X (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hPM : P ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
    rw [←hu.sylow_centralizer_eq_core]
    exact le_inf (hPN.trans (hNQ.trans hQT)) hPU
  have hN : IsPGroup 2 N := (isPGroup_pCoreIn 2 X).to_le hNQ
  let : Group.IsNilpotent N := hN.isNilpotent
  have hsol : Group.IsSolvable N := inferInstance
  have hcop : Nat.Coprime (Nat.card B) (Nat.card N) := by
    obtain ⟨k,hk⟩ := hN.exists_card_eq
    rw [hb,hk]
    exact (by decide : Nat.Coprime 7 2).pow_right k
  have hnot : ¬ P ≤ (frattini N).map N.subtype := by
    intro hPF
    obtain ⟨a,ha,hd⟩ := original_binary_triality_seven_frattini_action
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
    let d := (quotientAut (frattini N)).comp a
    have heq (b : B) : d b = 1 := by
      apply MulEquiv.ext
      intro v
      obtain ⟨v,rfl⟩ := QuotientGroup.mk'_surjective (frattini N) v
      change quotientAut (frattini N) (a b) (QuotientGroup.mk' (frattini N) v) = _
      rw [quotientAut_apply_mk]
      have hc : ((a b v * v⁻¹ : N) : G) ∈ P := by
        change ((a b v : N) : G) * (v : G)⁻¹ ∈ P
        rw [ha]
        change ⁅(b : G),(v : G)⁆ ∈ ⁅N,B⁆
        rw [commutator_comm N B]
        exact commutator_mem_commutator b.property v.property
      have hf : a b v * v⁻¹ ∈ frattini N := by
        obtain ⟨w,hw,he⟩ := hPF hc
        have he' : w = a b v * v⁻¹ := Subtype.ext he
        exact he' ▸ hw
      have hq : QuotientGroup.mk' (frattini N) (a b v * v⁻¹) = 1 :=
        (QuotientGroup.eq_one_iff (a b v * v⁻¹)).mpr hf
      rw [map_mul,map_inv,mul_inv_eq_one] at hq
      exact hq
    have hB0 : B = ⊥ := by
      apply bot_unique
      intro b hbB
      exact congrArg Subtype.val (hd ((heq ⟨b,hbB⟩).trans (map_one d).symm))
    have hc0 : Nat.card B = 1 := by rw [hB0]; simp
    omega
  have hmove : ¬ P ≤ centralizer (B : Set G) := by
    intro hc
    have hz : P = ⊥ := commutator_eq_bot_of_coprime_quadratic N B hBN hsol hcop
      (commutator_eq_bot_iff_le_centralizer.mpr hc)
    exact hnot (hz ▸ bot_le)
  exact ⟨le_inf (hPN.trans hNQ) hPM,hPU,hnot,hmove,
    (fun hP => hmove (hP.trans (le_centralizer_iff.mp hBU))),
    eq_commutator_sup_centralizer_of_solvable_coprime N B hBN hsol hcop⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
