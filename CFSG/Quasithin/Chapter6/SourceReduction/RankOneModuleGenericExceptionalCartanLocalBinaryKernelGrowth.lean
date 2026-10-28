module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryElementaryKernel
public import Theory.Representation.BinaryPermutation.FiveBorelTwoAction

/-!
# The retained binary kernel cannot be invariant under CT

Let U be the original L-span of Ω₁Z(T), X = CT the original containing
component--Sylow join, and E = U intersect O₂(X). The left Cartan A acts
nontrivially on E. Otherwise its full Borel acts on E through a two-group;
the original two-core centralizes U, so the marked A₄ Borel forces that
action to be trivial. Its fixed space has order at most two or four on
one or two A₅ copies, contradicting |U| ≤ 4|E|.

If C normalized E, its small action would be trivial, contradicting the
Cartan movement because A lies in C. This excludes the equality branch
of LocalBinarySmallInvariant: E has a strictly larger X-span of order at
least 4096 inside the same O₂(X). The large-span exclusion and construction
of the exceptional-component witness still require proof. No invariance
of U under X or deletion of the retained kernel is used.

Source: Aschbacher--Smith 5.1.13, printed pp.635--638, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem borel_centralizes_of_cartan
    {T : Sylow 2 G} {L H A B E : Subgroup G}
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (c : CartanPair T L H A B)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hEN : localBorel T L ≤ normalizer (E : Set G))
    (hAE : A ≤ centralizer (E : Set G))
    (hcore : L.pCoreIn 2 ≤ centralizer (E : Set G)) :
    localBorel T L ≤ centralizer (E : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let N := normalizer (P : Set L)
  have hN : N.map L.subtype = localBorel T L := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [hP,←localBorel_eq_map]
  let f : N →* MulAut E := E.normalizerMonoidHom.comp
    ((L.subtype.comp N.subtype).codRestrict (normalizer (E : Set G))
      (fun x => hEN (hN ▸ mem_map_of_mem L.subtype x.property)))
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : q.ker = pCore 2 L := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have heker : (q.comp N.subtype).ker ≤ f.ker := by
    intro x hx
    have hxcore : (x.val : G) ∈ L.pCoreIn 2 :=
      mem_map_of_mem L.subtype (hk ▸ (show x.val ∈ q.ker from hx))
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (x.val : G) * (z : G) * (x.val : G)⁻¹ = (z : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((hcore hxcore) z z.property).symm
  let S := (P : Subgroup L).subgroupOf N
  let D := (A.subgroupOf L).subgroupOf N
  have hAL : A ≤ L := c.left_le.trans inf_le_left
  have hDN : A.subgroupOf L ≤ N := by
    apply (map_le_map_iff_of_injective L.subtype_injective).mp
    rw [hN,map_subgroupOf_eq_of_le hAL]
    exact c.left_le
  have hgen : (P : Subgroup L) ⊔ A.subgroupOf L = N := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup,hP,subgroupOf_map_subtype,map_subgroupOf_eq_of_le hAL,hN]
    exact c.left_sup_intersection hTL
  have hSD : S ⊔ D = ⊤ := by
    change (P : Subgroup L).subgroupOf N ⊔ (A.subgroupOf L).subgroupOf N = ⊤
    rw [←subgroupOf_sup (show (P : Subgroup L) ≤ N from P.toSubgroup.le_normalizer) hDN,hgen,subgroupOf_self]
  have hDzero : D.map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff D (f := f)).mpr
    intro x hx
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (x.val : G) * (z : G) * (x.val : G)⁻¹ = (z : G)
    exact mul_inv_eq_iff_eq_mul.mpr ((hAE hx) z z.property).symm
  have hrange : S.map f = f.range := by
    rw [←sup_bot_eq (S.map f),←hDzero,←Subgroup.map_sup,hSD,←MonoidHom.range_eq_map]
  have hp : IsPGroup 2 f.range := hrange ▸ (P.isPGroup'.comap_subtype.map f)
  have hf := BinaryPermutation.FiveBorelTwoAction.trivial_of_two_image q hq P f heker hp
  rw [←hN]
  rintro x ⟨y,hy,rfl⟩ z hz
  have hzfix := congrArg (fun a : MulAut E => (a ⟨z,hz⟩ : G)) (hf ⟨y,hy⟩)
  change (y : G) * z * (y : G)⁻¹ = z at hzfix
  exact (mul_inv_eq_iff_eq_mul.mp hzfix).symm

private theorem model_fixed_card_bound
    {T : Sylow 2 G} {L U E : Subgroup G}
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (f : U ≃* Multiplicative V)
    (he : ∀ (l : L) (v : U),
      ((f.symm (Multiplicative.ofAdd (ρ (e (QuotientGroup.mk' (pCore 2 L) l))
        (Multiplicative.toAdd (f v))))) : G) = (l : G)*(v : G)*(l : G)⁻¹)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hEU : E ≤ U)
    (hfix : localBorel T L ≤ centralizer (E : Set G)) :
    ∃ P : Sylow 2 (alternatingGroup (Fin 5)),
      Nat.card E ≤ Nat.card (Representation.BinaryOffender.fixedSpace ρ P) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  have hf (x : E) : (f (inclusion hEU x)).toAdd ∈
      Representation.BinaryOffender.fixedSpace ρ S := by
    rintro ⟨a,ha⟩
    obtain ⟨l,hl,rfl⟩ := ha
    change ρ (q l) (f (inclusion hEU x)).toAdd = (f (inclusion hEU x)).toAdd
    have hlB : (l : G) ∈ localBorel T L := by
      rw [localBorel_eq_map,←hP]
      exact mem_map_of_mem L.subtype (P.toSubgroup.le_normalizer hl)
    have hc : (l : G)*(x : G)*(l : G)⁻¹ = (x : G) :=
      mul_inv_eq_iff_eq_mul.mpr ((hfix hlB) x x.property).symm
    have hh : f.symm (Multiplicative.ofAdd
        (ρ (q l) (f (inclusion hEU x)).toAdd)) = inclusion hEU x :=
      Subtype.ext ((he l (inclusion hEU x)).trans hc)
    have hcoords := congrArg (fun u : U => (f u).toAdd) hh
    simpa only [f.apply_symm_apply,toAdd_ofAdd] using hcoords
  let : Finite V := Finite.of_equiv U f.toEquiv
  let j : E → Representation.BinaryOffender.fixedSpace ρ S := fun x =>
    ⟨(f (inclusion hEU x)).toAdd,hf x⟩
  refine ⟨S,Nat.card_le_card_of_injective j ?_⟩
  intro x y heq
  exact inclusion_injective hEU (f.injective
    (Multiplicative.toAdd.injective (congrArg Subtype.val heq)))

private theorem oneOrTwo_borel_central_bound
    {T : Sylow 2 G} {L U E : Subgroup G}
    (hmodel : IsOneOrTwoA5Modules L U)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (hEU : E ≤ U)
    (hfix : localBorel T L ≤ centralizer (E : Set G)) :
    (Nat.card U = 16 ∧ Nat.card E ≤ 2) ∨ (Nat.card U = 256 ∧ Nat.card E ≤ 4) := by
  have hcard : Nat.card (BinaryPermutation.natural (Fin 5)) = 16 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_natural_odd (Fin 5) (by decide)]
    rfl
  rcases hmodel with ⟨e,f,he⟩ | ⟨e,f,he⟩
  · obtain ⟨P,hP⟩ := model_fixed_card_bound a5Module e f he hTL hEU hfix
    exact .inl ⟨(Nat.card_congr f.toEquiv).trans hcard,
      hP.trans (BinaryPermutation.FiveBorelTwoAction.sylow_fixed_card_le_two P)⟩
  · obtain ⟨P,hP⟩ := model_fixed_card_bound (a5Module.prod a5Module) e f he hTL hEU hfix
    refine .inr ⟨?_,hP.trans (BinaryPermutation.FiveBorelTwoAction.sylow_fixed_pair_card_le_four P)⟩
    rw [Nat.card_congr f.toEquiv]
    change Nat.card (BinaryPermutation.natural (Fin 5) × BinaryPermutation.natural (Fin 5)) = 256
    rw [Nat.card_prod,hcard]

/-- The original left Cartan acts nontrivially on the exact retained kernel. -/
theorem original_binary_triality_kernel_cartan_moves
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
    ¬ A ≤ centralizer (E : Set G) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  change ¬ A ≤ centralizer (E : Set G)
  intro hAE
  obtain ⟨hmodel,_,hbound,_⟩ := original_binary_triality_elementary_kernel_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hXQ : X ≤ normalizer (X.pCoreIn 2 : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hTE : (T : Subgroup G) ≤ normalizer (E : Set G) :=
    (le_inf (le_sup_right.trans (reduced_normalizes hu.reduced))
      (le_sup_right.trans hXQ)).trans inf_normalizer_le_normalizer_inf
  have hBE : localBorel T L ≤ normalizer (E : Set G) := by
    rw [←c.left_sup_intersection h.sylow_normalizes]
    exact sup_le (inf_le_left.trans hTE) (hAE.trans (Subgroup.centralizer_le_normalizer _))
  have hc : L.pCoreIn 2 ≤ centralizer (E : Set G) :=
    h.core_centralizes_omega_span.trans (centralizer_le (show E ≤ U from inf_le_left))
  have hfix : localBorel T L ≤ centralizer (E : Set G) := by
    rcases hmodel with ⟨e,f,he⟩ | ⟨e,f,he⟩ <;>
      exact borel_centralizes_of_cartan h.sylow_normalizes c e hBE hAE hc
  have hsmall := oneOrTwo_borel_central_bound hmodel h.sylow_normalizes
    (show E ≤ U from inf_le_left) hfix
  change Nat.card U ≤ 4 * Nat.card E at hbound
  change (Nat.card U = 16 ∧ Nat.card E ≤ 2) ∨ (Nat.card U = 256 ∧ Nat.card E ≤ 4) at hsmall
  rcases hsmall with ⟨hs,he⟩ | ⟨hs,he⟩ <;> omega

/-- The actual retained kernel is not normalized by the containing triality component. -/
theorem original_binary_triality_kernel_not_invariant
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
    ¬ C.map Y.subtype ≤ normalizer (E : Set G) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  change ¬ C.map Y.subtype ≤ normalizer (E : Set G)
  intro hn
  have hCE := (original_binary_triality_small_invariant
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2 E inf_le_left hn
  obtain ⟨_,_,hAC,_⟩ := original_binary_triality_module_and_hall
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  exact original_binary_triality_kernel_cartan_moves
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm (hAC.trans hCE)

/-- Only the large CT-span branch remains. The exact kernel is moved by
the triality component and generates a subgroup of order at least 4096 inside the same two-core. -/
theorem original_binary_triality_kernel_large_span
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
    ¬ C.map Y.subtype ≤ normalizer (E : Set G) ∧
      E < N ∧ N ≤ X.pCoreIn 2 ∧ X ≤ normalizer (N : Set G) ∧
      4096 ≤ Nat.card N := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  let N := conjugateSpanBy E X
  have hn := original_binary_triality_kernel_not_invariant
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hNQ,hXN,_,hcases⟩ := original_binary_triality_kernel_growth
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hsize : 4096 ≤ Nat.card N := by
    rcases hcases with ⟨_,hc,_⟩ | hc
    · exact False.elim (hn (hc.trans (Subgroup.centralizer_le_normalizer _)))
    · exact hc
  change X ≤ normalizer (N : Set G) at hXN
  have hENne : E ≠ N := by
    intro he
    exact hn (le_sup_left.trans (he.symm ▸ hXN))
  exact ⟨hn,lt_of_le_of_ne (le_conjugateSpanBy E X) hENne,hNQ,hXN,hsize⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
