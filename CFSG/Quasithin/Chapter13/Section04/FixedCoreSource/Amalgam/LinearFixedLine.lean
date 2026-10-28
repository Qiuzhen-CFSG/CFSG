module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLineOrbits
public import Theory.Representation.PSL3Two.FixedParabolicQuotient

/-!
# The original fixed-line module in the linear component case

Restrict the original parabolic to the actual normal component K and
restrict the common Sylow simultaneously. Normal supplement indices and
the proved order of K/O₂(K) give index seven. The fixed line is moved by
K because X=KT, T fixes the line and the opposite vertex moves it.

Its orbit therefore has dimension greater than one. The native Fano
quotient theorem constructs one marking of K/O₂(K), the parabolic and
its Sylow, with an equivariant permutation surjection and a dual-natural
quotient. Its commutator subspace has the actual dual-natural or Fano-core
action. In particular each such orbit has precisely O₂(K) as action
kernel, and its dimension is three, four, six or seven.

This proves the permutation-module step in the linear row of 13.4.7,
printed p.901. It does not yet identify the orientation relative to the
chosen constituent I or the whole omega module, or prove Thompson
normality and the overgroup supplement. The linear model premise is the
actual case isomorphism, not a replacement for the remaining model sieve.
Structural1222 and Source1332OneTwo retain their existing producers and
final discharge with the fixed-core assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open BinaryLinearThree.FanoDecomposition
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The original parabolic restricts to an index-seven subgroup of the
actual component, with the literal intersection of the original Sylow. -/
theorem original_pair_linear_parabolic
    (h₀ : Hypothesis1331 T L) (D : ChosenModule T L V) (m : CoreMarking D)
    (h1332 : Source1332OneTwo T)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    ∃ S : Sylow 2 C, (S : Subgroup C) = (T : Subgroup G).subgroupOf C ∧
      (B.subgroupOf C).index = 7 := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let SX : Sylow 2 X := T.subtype (hTA.trans le_sup_left)
  let : K.Normal := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).1
  obtain ⟨R,hR⟩ := SX.exists_subgroupOf_eq_of_normal K
  let j := K.equivMapOfInjective X.subtype X.subtype_injective
  let S : Sylow 2 C := R.mapSurjective (f := j.toMonoidHom) j.surjective
  have hS : (S : Subgroup C) = (T : Subgroup G).subgroupOf C := by
    ext c
    obtain ⟨k,rfl⟩ := j.surjective c
    change j k ∈ (R : Subgroup K).map j.toMonoidHom ↔ _
    refine (mem_map_iff_mem (f := j.toMonoidHom) (K := (R : Subgroup K))
      (x := k) j.injective).trans ?_
    rw [hR]
    rfl
  have hg : K ⊔ (SX : Subgroup X) = ⊤ := by
    rw [← (original_pair_component_is_residual h₀ D m h1332
      hTA hTB eA eB hne hindexA hindexB K hK).1]
    exact pResidual_sup_sylow_eq_top SX
  have hBP : (B.subgroupOf X).subgroupOf K = (B.subgroupOf C).comap j.toMonoidHom := rfl
  have hi : (B.subgroupOf C).index = B.relIndex X := by
    change (B.subgroupOf C).index = (B.subgroupOf X).index
    have hh := normal_intersection_relIndex (B.subgroupOf X) ⊤ K le_top (by
      rw [←hg]
      exact sup_le_sup le_rfl (show (SX : Subgroup X) ≤ B.subgroupOf X from fun _ ht => hTB ht))
    simpa only [top_subgroupOf,relIndex_top_right,hBP,(B.subgroupOf C).index_comap_of_surjective (f := j.toMonoidHom) j.surjective]
      using hh
  have hcard : Nat.card (C ⧸ pCore 2 C) = 168 :=
    (Nat.card_congr eK.toEquiv).trans Matrix.PSL3Two.card_PSL
  have hb := (original_pair_parabolic_index_formula h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  change B.relIndex X * 3 * 2 ^ (Nat.card (C ⧸ pCore 2 C)).factorization 2 =
    Nat.card (C ⧸ pCore 2 C) at hb
  rw [hcard,show (Nat.factorization 168) 2 = 3 from by decide +kernel] at hb
  exact ⟨S,hS,by rw [hi]; omega⟩

/-- In the linear component case, the original second fixed line has a
faithful Fano permutation quotient and a dual-natural head. -/
theorem original_pair_linear_fixed_line_quotient
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent)
    (eK : ((K.map (A ⊔ B).subtype) ⧸ pCore 2 (K.map (A ⊔ B).subtype)) ≃*
      Matrix.PSL3Two.PSL) :
    let C := K.map (A ⊔ B).subtype
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F C
    ∃ he : IsElementaryAbelian 2 U, let := he
      let ρ := Representation.elementaryRepresentation (p := 2)
        (U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C)))
      (Module.finrank (ZMod 2) (Additive U) = 3 ∨
        Module.finrank (ZMod 2) (Additive U) = 4 ∨
        Module.finrank (ZMod 2) (Additive U) = 6 ∨
        Module.finrank (ZMod 2) (Additive U) = 7) ∧
      C ⊓ centralizer (U : Set G) = C.pCoreIn 2 ∧
      ∃ e : (C ⧸ pCore 2 C) ≃* BinaryLinearThree.Group,
        let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 C))
        (B.subgroupOf C).map f = Matrix.PSL3Two.lineParabolicSL ∧
        ((T : Subgroup G).subgroupOf C).map f = Matrix.PSL3Two.borelSL ∧
        (∃ q : Representation.IntertwiningMap
          (BinaryLinearThree.FanoLineQuotients.lineRepresentation.comp f) ρ,
          Function.Surjective q ∧
          (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range.toSubmodule =
            Representation.BinaryOffender.subspaceCommutator ρ ⊤ ⊤ ∧
          (Nonempty (Representation.Equiv (BinaryLinearThree.W.dual.comp f)
              (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range.toRepresentation) ∨
            Nonempty (Representation.Equiv (lineCoreRepresentation.comp f)
              (BinaryLinearThree.FanoLineMoved.coreMap f ρ q).range.toRepresentation))) ∧
        (∃ r : ρ.IntertwiningMap (BinaryLinearThree.W.dual.comp f), Function.Surjective r) := by
  let X := A ⊔ B
  let C := K.map X.subtype
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let U := conjugateSpanBy F C
  obtain ⟨heX,_,_,v,hv,hm,_,_,_,_⟩ := original_pair_fixed_line_permutation_quotient
    h₀ h structural D m hTA hTB eA eB hne hout hindexL hindexA hindexB hres
  let := heX
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion (conjugateSpanBy_mono le_rfl (map_subtype_le K))) (inclusion_injective _)
  let := he
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  have hF : Nat.card F = 2 := (original_pair_fixed_lines h structural D m hout
    hindexL hindexA hindexB hd).2.2.1
  have hgen := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  have hmove : ¬ F ≤ centralizer (C : Set G) := by
    intro hh
    have hCX : X ≤ centralizer ({v.val} : Set G) := by
      change A ⊔ B ≤ _
      rw [hgen]
      refine sup_le (fun c hc => mem_centralizer_singleton_iff.mpr (hh v.property c hc)) ?_
      intro t ht
      exact mem_centralizer_singleton_iff.mpr
        (((mem_omegaOneCenterAmbient_iff _ _).mp v.property.1).2.2 t ht)
    exact hm (fun a ha => mem_centralizer_singleton_iff.mp (hCX ((show A ≤ X from le_sup_left) ha)))
  have hlower := Representation.one_lt_finrank_conjugateLine F C hF hmove
  obtain ⟨S,hS,hi⟩ := original_pair_linear_parabolic h₀ D m h1332 hTA hTB eA eB hne
    hindexA hindexB K hK eK
  let actor := U.normalizerMonoidHom.comp (inclusion (le_normalizer_conjugateSpanBy F C))
  let ρ := Representation.elementaryRepresentation (p := 2) actor
  let w := inclusion (le_conjugateSpanBy F C) v
  have hw (a : B.subgroupOf C) : ρ a (Additive.ofMul w) = Additive.ofMul w := by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (v.property.2 a.val.val a.property)
  have hs : Submodule.span (ZMod 2) (Set.range (fun c : C => ρ c (Additive.ofMul w))) = ⊤ := by
    apply Representation.conjugateSpan_binary_orbit_span F C U (le_conjugateSpanBy F C) rfl
      (MonoidHom.id U) Function.surjective_id actor
    · intro c x hx
      rfl
    · intro a
      obtain ⟨b,hb,huniq⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
      by_cases ha : a = 1
      · exact Or.inl (by simp [ha])
      · exact Or.inr (congrArg (inclusion (le_conjugateSpanBy F C))
          ((huniq a ha).trans (huniq v hv).symm))
  obtain ⟨hd,hker,e,hP,hSb,hq,hr⟩ := BinaryLinearThree.FixedParabolicQuotient.quotient_and_head
    eK S (B.subgroupOf C) (by rw [hS]; exact fun _ ht => hTB ht) hi ρ
    (Additive.ofMul w) hw hs hlower
  rw [hS] at hSb
  have hkerC : ρ.ker = (centralizer (U : Set G)).subgroupOf C := by
    ext c
    change ρ c = 1 ↔ c.val ∈ centralizer (U : Set G)
    constructor
    · intro hc u hu
      have hh := congrArg (fun x : Additive U => x.toMul.val)
        (LinearMap.congr_fun hc (Additive.ofMul ⟨u,hu⟩))
      change c.val * u * c.val⁻¹ = u at hh
      exact (mul_inv_eq_iff_eq_mul.mp hh).symm
    · intro hc
      apply LinearMap.ext
      intro u
      apply Additive.toMul.injective
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (hc u.toMul u.toMul.property).symm
  have hcentral := congrArg (Subgroup.map C.subtype) (hkerC.symm.trans hker)
  rw [subgroupOf_map_subtype,inf_comm] at hcentral
  exact ⟨he,hd,hcentral,e,hP,hSb,hq,hr⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
