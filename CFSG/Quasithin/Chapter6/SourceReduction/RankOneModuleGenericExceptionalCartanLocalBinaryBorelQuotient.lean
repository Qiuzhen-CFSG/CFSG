module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalBinaryElementaryKernel
public import Theory.Representation.BinaryPermutation.FiveBorelSmallQuotient

/-!
# Borel fixation of the retained binary quotient

Let X = CT, U = ⟨Ω₁Z(T)ᴸ⟩, and E = U intersect O₂(X). The literal
image of U in X/O₂(X) has order at most four. Its kernel E is invariant
under the original left Borel: that Borel lies in X and normalizes U.
The one-or-two A₅ marking therefore shows that every Borel displacement
lies in E. In particular the original left Cartan A centralizes the
image of U in the SAME X/O₂(X).

The small-quotient calculation is in FiveBorelSmallQuotient. All original
maps, Hall subgroups and ambient hypotheses are retained. This supplies
the Cartan-fixed image needed for the central-parabolic exclusion; it
does not yet prove U ≤ O₂(X) or exclude the large retained span.
Source: Aschbacher--Smith 5.1.10--13, printed pp.634--638,
refs/quasithin.pdf, with the binary permutation conventions of B.3.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
variable {G : Type*} [Group G] [Finite G]

private theorem model_small_quotient_commutator
    {T : Sylow 2 G} {L U E : Subgroup G} {D V : Type*}
    [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) (alternatingGroup (Fin 5)) V)
    (hmodel : IsConjugationModel L U ρ)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (f : U →* D)
    (hker : ∀ u : U, f u = 1 ↔ (u : G) ∈ E)
    (hn : localBorel T L ≤ normalizer (E : Set G))
    (hsmall : ∀ (P : Sylow 2 (alternatingGroup (Fin 5)))
      (r : Multiplicative V →* D),
      (∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))),
        ∀ v ∈ r.ker, Multiplicative.ofAdd (ρ a v.toAdd) ∈ r.ker) →
      ∀ a ∈ normalizer (P : Set (alternatingGroup (Fin 5))), ∀ v : V,
        r (Multiplicative.ofAdd (ρ a v)) = r (Multiplicative.ofAdd v)) :
    ⁅localBorel T L,U⁆ ≤ E := by
  obtain ⟨e,m,hm⟩ := hmodel
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L hTL
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S := P.mapSurjective hq
  let r := f.comp m.symm.toMonoidHom
  have hN : (normalizer (P : Set L)).map L.subtype = localBorel T L := by
    change (normalizer ((P : Subgroup L) : Set L)).map L.subtype = _
    rw [hP,←localBorel_eq_map]
  have hr : ∀ a ∈ normalizer (S : Set (alternatingGroup (Fin 5))),
      ∀ v ∈ r.ker, Multiplicative.ofAdd (ρ a v.toAdd) ∈ r.ker := by
    intro a ha v hv
    obtain ⟨l,hl,he⟩ := (P.normalizer_map_surjective q hq).ge ha
    have hlB : (l : G) ∈ localBorel T L := hN ▸ mem_map_of_mem L.subtype hl
    have hve : (m.symm v : G) ∈ E := (hker _).mp hv
    have hconj := le_normalizer_iff.mp hn l hlB (m.symm v) hve
    apply (hker _).mpr
    change (m.symm (Multiplicative.ofAdd (ρ a v.toAdd)) : G) ∈ E
    have hh := hm l (m.symm v)
    rw [m.apply_symm_apply] at hh
    change (m.symm (Multiplicative.ofAdd (ρ (q l) v.toAdd)) : G) = _ at hh
    rw [he] at hh
    exact hh.symm ▸ hconj
  have hf := hsmall S r hr
  apply commutator_le.mpr
  intro l hl u hu
  obtain ⟨l',hl',hel⟩ := hN.symm ▸ hl
  subst l
  have hlS : q l' ∈ normalizer (S : Set (alternatingGroup (Fin 5))) :=
    (P.normalizer_map_surjective q hq) ▸ mem_map_of_mem q hl'
  have heq := hf (q l') hlS (m (⟨u,hu⟩ : U)).toAdd
  change f (m.symm (Multiplicative.ofAdd (ρ (q l') (m ⟨u,hu⟩).toAdd))) =
    f (m.symm (m ⟨u,hu⟩)) at heq
  rw [m.symm_apply_apply] at heq
  let v := m.symm (Multiplicative.ofAdd (ρ (q l') (m ⟨u,hu⟩).toAdd))
  have hv : f (v * (⟨u,hu⟩ : U)⁻¹) = 1 := by
    rw [map_mul,map_inv,heq,mul_inv_cancel]
  have hmem := (hker _).mp hv
  have hc : (v : G) = (l' : G)*u*(l' : G)⁻¹ := hm l' ⟨u,hu⟩
  change (v : G)*u⁻¹ ∈ E at hmem
  change (l' : G) * u * (l' : G)⁻¹ * u⁻¹ ∈ E
  rwa [hc] at hmem

private theorem oneOrTwo_small_quotient_commutator
    {T : Sylow 2 G} {L U E : Subgroup G} {D : Type*} [Group D] [Finite D]
    (hmodel : IsOneOrTwoA5Modules L U)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (f : U →* D) (hcard : Nat.card D ≤ 4)
    (hker : ∀ u : U, f u = 1 ↔ (u : G) ∈ E)
    (hn : localBorel T L ≤ normalizer (E : Set G)) :
    ⁅localBorel T L,U⁆ ≤ E := by
  rcases hmodel with hm | hm
  · exact model_small_quotient_commutator a5Module hm hTL f hker hn
      (fun P r hi => BinaryPermutation.FiveBorelSmallQuotient.natural_small_image P r hcard hi)
  · exact model_small_quotient_commutator (a5Module.prod a5Module) hm hTL f hker hn
      (fun P r hi => BinaryPermutation.FiveBorelSmallQuotient.pair_small_image P r hcard hi)

/-- The original left Borel fixes the literal omega-span image in CT/O₂(CT).
Equivalently, its full commutator with U lies in the retained kernel E. -/
theorem original_binary_triality_kernel_borel_commutator
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
    ⁅localBorel T L,U⁆ ≤ E ∧ ⁅A,U⁆ ≤ E := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let E := U ⊓ X.pCoreIn 2
  obtain ⟨hu,_,_,_,_⟩ := original_binary_triality_fixed_omega_span
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨hmodel,_,_,_⟩ := original_binary_triality_elementary_kernel_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,hcard⟩ := original_binary_triality_elementary_image_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  obtain ⟨_,_,hAX,_⟩ := original_binary_triality_core_bound
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm
  have hUX : U ≤ X := hu.reduced_le_sylow.trans le_sup_right
  have hBX : localBorel T L ≤ X := by
    rw [←c.left_sup_intersection h.sylow_normalizes]
    exact sup_le (inf_le_left.trans le_sup_right) hAX
  have hXQ : X ≤ normalizer (X.pCoreIn 2 : Set G) := X.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image X (pCore 2 X))
  have hBE : localBorel T L ≤ normalizer (E : Set G) :=
    (le_inf ((inf_le_left.trans le_sup_left).trans (reduced_normalizes hu.reduced))
      (hBX.trans hXQ)).trans inf_normalizer_le_normalizer_inf
  let q := QuotientGroup.mk' (pCore 2 X)
  let f := (q.subgroupMap (U.subgroupOf X)).comp
    (subgroupOfEquivOfLe hUX).symm.toMonoidHom
  have hk : ∀ u : U, f u = 1 ↔ (u : G) ∈ E := by
    intro u
    change q.subgroupMap (U.subgroupOf X) ((subgroupOfEquivOfLe hUX).symm u) = 1 ↔ _
    rw [Subtype.ext_iff]
    change q (⟨u,hUX u.property⟩ : X) = 1 ↔ _
    change ((⟨u,hUX u.property⟩ : X) : X ⧸ pCore 2 X) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    constructor
    · intro hh
      exact ⟨u.property,mem_map_of_mem X.subtype hh⟩
    · rintro ⟨_,x,hx,he⟩
      have hxe : x = (⟨u,hUX u.property⟩ : X) := Subtype.ext he
      exact hxe ▸ hx
  have hh := oneOrTwo_small_quotient_commutator hmodel h.sylow_normalizes f hcard hk hBE
  exact ⟨hh,(commutator_mono c.left_le le_rfl).trans hh⟩
/-- The original cubic fixes the actual quotient image pointwise. -/
theorem original_binary_triality_omega_image_cartan_fixed
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
    let q := QuotientGroup.mk' (pCore 2 X)
    (A.subgroupOf X).map q ≤
      centralizer (((U.subgroupOf X).map q) : Set (X ⧸ pCore 2 X)) := by
  let X := C.map Y.subtype ⊔ (T : Subgroup G)
  let U := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L
  let q := QuotientGroup.mk' (pCore 2 X)
  have hc := (original_binary_triality_kernel_borel_commutator
    h hH hgen c hKH hK hKT horbit hY hescape C hC hKC hm).2
  have hcomm : ⁅A.subgroupOf X,U.subgroupOf X⁆ ≤ pCore 2 X := by
    intro x hx
    have hh := mem_map_of_mem X.subtype hx
    rw [map_commutator] at hh
    have hcore := (hc ((commutator_mono (show (A.subgroupOf X).map X.subtype ≤ A by
        rw [subgroupOf_map_subtype]; exact inf_le_left)
      (show (U.subgroupOf X).map X.subtype ≤ U by
        rw [subgroupOf_map_subtype]; exact inf_le_left)) hh)).2
    obtain ⟨y,hy,he⟩ := hcore
    exact (show y = x from Subtype.ext he) ▸ hy
  apply commutator_eq_bot_iff_le_centralizer.mp
  rw [←map_commutator]
  apply (Subgroup.map_eq_bot_iff _).mpr
  simpa only [q,QuotientGroup.ker_mk'] using hcomm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.BinaryOmega
