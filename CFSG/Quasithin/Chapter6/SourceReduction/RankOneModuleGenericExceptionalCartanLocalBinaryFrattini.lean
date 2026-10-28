module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryKernelGrowth
public import Theory.GroupAction.ThirteenFrattini

/-!
# The Frattini layer of the retained binary kernel span

Let X = CT, U = ⟨Ω₁Z(T)ᴸ⟩, E = U intersect O₂(X), and N = ⟨Eˣ⟩.
The component acts nontrivially on N. Burnside's automorphism-kernel
theorem detects this action on N/Φ(N); thirteen-generation then forces
|N/Φ(N)| ≥ 4096. Thus the previous large-order alternative survives
removal of the entire Frattini subgroup, including nonabelian core effects.
The full action kernel is a two-group, and the literal action image modulo
its own two-core is isomorphic to genuine binary triality.

The literal image of E in N/Φ(N) is nonzero, proper, and has order
at most 256. Its exact kernel E intersect Φ(N) is retained in the cardinal
identity. The component does not even normalize EΦ(N): otherwise its
T-invariance and the definition of N would make EΦ(N) = N, contradicting
Frattini nongeneration and the already strict inclusion E < N.

These are constraints on the remaining large-span branch, not its
exclusion. No CT-invariance of U, splitting, or trivial core is assumed.
Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638,
refs/quasithin.pdf, with Burnside's basis theorem.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem component_thirteen_generated
    {Y : Subgroup G} (C : Subgroup Y) (hC : C.IsCComponent)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    IsPPerfect 2 C ∧ primeToResidual 13 C = ⊤ := by
  let := hC.perfect
  have hp : IsPPerfect 2 C := by
    intro K hK hquot
    let := hK
    let : Group.IsNilpotent (C ⧸ K) := hquot.isNilpotent
    exact top_le_iff.mp (le_of_isPerfect_of_solvable_quotient ⊤ K)
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) (C ⧸ pCore 2 C) by simpa using hm)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := e.isSimpleGroup
  let : Fact (Nat.Prime 13) := ⟨by decide⟩
  have hd : 13 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_carrier,
      Triality.Standard.ConcreteBruhat.FixedCellCount.card_borel]
    norm_num [Triality.Standard.binaryParameters_q]
  exact ⟨hp,primeToResidual_eq_top_of_simple_quotient 13 2 (pCore 2 C)
    pCore_isPGroup hp hd⟩

private theorem nontrivial_action_kernel_le_core
    {J D : Type*} [Group J] [Group D]
    [IsSimpleGroup (J ⧸ pCore 2 J)]
    (hp : IsPPerfect 2 J) (f : J →* D) (hf : f ≠ 1) : f.ker ≤ pCore 2 J := by
  let q := QuotientGroup.mk' (pCore 2 J)
  have hn : (f.ker.map q).Normal := Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  rcases hn.eq_bot_or_eq_top with hz | ht
  · simpa only [q,QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hz
  · have hs : f.ker ⊔ pCore 2 J = ⊤ := by
      have hh := congrArg (Subgroup.comap q) ht
      simpa only [comap_map_eq,q,QuotientGroup.ker_mk',comap_top] using hh
    have hk := hp f.ker inferInstance
      (isPGroup_quotient_of_sup_eq_top f.ker (pCore 2 J) pCore_isPGroup hs)
    exact (hf (MonoidHom.ext (fun j => by
      exact (show j ∈ f.ker from hk ▸ mem_top j)))).elim

/-- The actual component conjugation acts nontrivially on the literal
Frattini quotient of the retained kernel span, whose order is at least 4096. -/
theorem original_binary_triality_kernel_frattini_action
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
    ∃ a : C →* MulAut N,
      (∀ (c : C) (v : N), ((a c v : N) : G) =
        (c.val : G) * (v : G) * (c.val : G)⁻¹) ∧
      a ≠ 1 ∧ (quotientAut (frattini N)).comp a ≠ 1 ∧
      4096 ≤ Nat.card (N ⧸ frattini N) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨_,_,hNQ,hXN,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hCN : C.map Y.subtype ≤ normalizer (N : Set G) := le_sup_left.trans hXN
  let a : C →* MulAut N := N.normalizerMonoidHom.comp
    ((Y.subtype.comp C.subtype).codRestrict (normalizer (N : Set G))
      (fun x => hCN (mem_map_of_mem Y.subtype x.property)))
  have ha : a ≠ 1 := by
    intro hz
    have hc : C.map Y.subtype ≤ centralizer (N : Set G) := by
      rintro x ⟨y,hy,rfl⟩ z hzN
      have he := congrArg (fun f : MulAut N => (f ⟨z,hzN⟩ : G))
        (DFunLike.congr_fun hz ⟨y,hy⟩)
      change (y : G)*z*(y : G)⁻¹ = z at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have hCE := hc.trans (centralizer_le (le_conjugateSpanBy E X))
    exact original_binary_triality_kernel_not_invariant
      h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
      (hCE.trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨hp,h13⟩ := component_thirteen_generated C hC hm
  have hN : IsPGroup 2 N := (isPGroup_pCoreIn 2 X).to_le hNQ
  exact ⟨a,fun _ _ => rfl,ha,
    fun hz => ha (MulAut.action_eq_one_of_frattini hp hN a hz),
    MulAut.thirteen_frattini_card_ge hp h13 hN a ha⟩

/-- The original seed survives in the Frattini quotient with its full
kernel retained; its image is nonzero, proper, and has order at most 256. -/
theorem original_binary_triality_kernel_frattini_seed
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
    let q := QuotientGroup.mk' (frattini N)
    let V := (E.subgroupOf N).map q
    V ≠ ⊥ ∧ V ≠ ⊤ ∧ Nat.card V ≤ 256 ∧
      Nat.card (E ⊓ (frattini N).map N.subtype : Subgroup G) * Nat.card V = Nat.card E ∧
      4096 ≤ Nat.card (N ⧸ frattini N) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  let q := QuotientGroup.mk' (frattini N)
  let V := (E.subgroupOf N).map q
  have hEN : E ≤ N := le_conjugateSpanBy E X
  have hXN : X ≤ normalizer (N : Set G) := le_normalizer_conjugateSpanBy E X
  have hXphi : X ≤ normalizer ((frattini N).map N.subtype : Set G) :=
    hXN.trans (normalizer_le_normalizer_characteristic_image N (frattini N))
  obtain ⟨a,ha,ha0,haq,hlarge⟩ := original_binary_triality_kernel_frattini_action
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  change 4096 ≤ Nat.card (N ⧸ frattini N) at hlarge
  have hsmall : Nat.card V ≤ 256 := by
    have hE : Nat.card E ≤ 256 := (card_le_of_le (show E ≤ U from inf_le_left)).trans
      (original_binary_triality_small_invariant
        h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).1
    exact (Nat.card_le_card_of_surjective _ (q.subgroupMap_surjective (E.subgroupOf N))).trans
      ((Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv).le.trans hE)
  have hne : V ≠ ⊥ := by
    intro hz
    have hEphi : E ≤ (frattini N).map N.subtype := by
      have hh := (Subgroup.map_eq_bot_iff (E.subgroupOf N) (f := q)).mp hz
      rw [QuotientGroup.ker_mk'] at hh
      have hi := map_mono (f := N.subtype) hh
      rwa [map_subgroupOf_eq_of_le hEN] at hi
    have hNphi : N ≤ (frattini N).map N.subtype := conjugateSpanBy_le hEphi hXphi
    have hphi : frattini N = ⊤ := by
      apply map_injective N.subtype_injective
      rw [←MonoidHom.range_eq_map,range_subtype]
      exact le_antisymm (map_subtype_le _) hNphi
    have hqcard : Nat.card (N ⧸ frattini N) = 1 := by
      rw [hphi]
      exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, ⟨1⟩⟩
    omega
  have hproper : V ≠ ⊤ := by
    intro ht
    have hvcard : Nat.card V = Nat.card (N ⧸ frattini N) := by
      rw [ht]
      exact Nat.card_congr (topEquiv (G := N ⧸ frattini N)).toEquiv
    omega
  have hi : ((E.subgroupOf N) ⊓ frattini N).map N.subtype =
      E ⊓ (frattini N).map N.subtype := by
    rw [map_inf _ _ N.subtype N.subtype_injective,map_subgroupOf_eq_of_le hEN]
  have hkcard : Nat.card ((E.subgroupOf N) ⊓ frattini N : Subgroup N) =
      Nat.card (E ⊓ (frattini N).map N.subtype : Subgroup G) := by
    rw [←card_map_of_injective (K := (E.subgroupOf N) ⊓ frattini N) N.subtype_injective,hi]
  have hcount := IsElementaryAbelian.card_inf_ker_mul_card_map (E.subgroupOf N) q
  rw [QuotientGroup.ker_mk',hkcard,Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv] at hcount
  exact ⟨hne,hproper,hsmall,hcount,hlarge⟩

/-- The component moves even the full Frattini preimage of the seed.
Invariance modulo the Frattini subgroup cannot replace the missing invariance of E. -/
theorem original_binary_triality_kernel_frattini_escape
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
    let F := E ⊔ (frattini N).map N.subtype
    F < N ∧ ¬ C.map Y.subtype ≤ normalizer (F : Set G) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  let F := E ⊔ (frattini N).map N.subtype
  have hEN : E ≤ N := le_conjugateSpanBy E X
  obtain ⟨_,hstrict,_,hXN,_⟩ := original_binary_triality_kernel_large_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hFN : F ≤ N := sup_le hEN (map_subtype_le _)
  have hFne : F ≠ N := by
    intro he
    have hs : E.subgroupOf N ⊔ frattini N = ⊤ := by
      apply map_injective N.subtype_injective
      rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hEN,
        ←MonoidHom.range_eq_map,range_subtype]
      exact he
    have hE := congrArg (fun D : Subgroup N => D.map N.subtype) (frattini_nongenerating hs)
    rw [map_subgroupOf_eq_of_le hEN,←MonoidHom.range_eq_map,range_subtype] at hE
    exact hstrict.ne hE
  refine ⟨lt_of_le_of_ne hFN hFne,?_⟩
  intro hCF
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hXQ : X ≤ normalizer (X.pCoreIn 2 : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (le_sup_right.trans (reduced_normalizes hu.reduced))
      (le_sup_right.trans hXQ)).trans inf_normalizer_le_normalizer_inf
  have hXphi : X ≤ normalizer ((frattini N).map N.subtype : Set G) :=
    hXN.trans (normalizer_le_normalizer_characteristic_image N (frattini N))
  have hTF : (T : Subgroup G) ≤ normalizer (F : Set G) :=
    (le_inf hTE (le_sup_right.trans hXphi)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hXF : X ≤ normalizer (F : Set G) := sup_le hCF hTF
  exact hFne (le_antisymm hFN (conjugateSpanBy_le le_sup_left hXF))

/-- The actual Frattini action image retains the genuine binary-triality
two-core quotient. Its full action kernel is proved to be a two-group. -/
theorem original_binary_triality_kernel_frattini_image
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
    ∃ a : C →* MulAut N,
      (∀ (c : C) (v : N), ((a c v : N) : G) =
        (c.val : G) * (v : G) * (c.val : G)⁻¹) ∧
      let d := (quotientAut (frattini N)).comp a
      d.ker ≤ pCore 2 C ∧ IsPGroup 2 d.ker ∧
        Nonempty ((d.range ⧸ pCore 2 d.range) ≃*
          Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  obtain ⟨a,ha,_,hd,_⟩ := original_binary_triality_kernel_frattini_action
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  let d := (quotientAut (frattini N)).comp a
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp
    (show Triality.Standard.IsTrialityGroupAt (2^1) (C ⧸ pCore 2 C) by simpa using hm)
  let : IsSimpleGroup (C ⧸ pCore 2 C) := e.isSimpleGroup
  have hk := nontrivial_action_kernel_le_core (component_thirteen_generated C hC hm).1 d hd
  have hkp : IsPGroup 2 d.ker := pCore_isPGroup.to_le hk
  have hkr : IsPGroup 2 d.rangeRestrict.ker := hkp.to_le (by
    intro x hx
    exact congrArg Subtype.val hx)
  let b := d.rangeRestrict.pCoreQuotientEquiv d.rangeRestrict_surjective hkr
  exact ⟨a,ha,hk,hkp,⟨b.symm.trans e⟩⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
