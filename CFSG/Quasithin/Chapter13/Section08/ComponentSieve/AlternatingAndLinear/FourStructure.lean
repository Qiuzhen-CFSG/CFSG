module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearEndgame
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.Seed
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SectionTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.PlaneTransport
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.RadicalRank
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.SplittingSource
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.UpperSection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.OriginalSource.Seed

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.ChiefFactors
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.AssemblyInputs

/-!
# The conditional L₄ natural-module argument in 13.8.25

`source_natural_module_of_strict_critical_pair` proves that the entire literal
module U_H/V₁ is four-dimensional and natural, returning an equivariant linear
equivalence for the actual H/O₂(H) action. It assumes the genuine earlier
source setup, the selected strict critical pair of 13.8.8(2), the covered-A₆
and L₄ group identifications, and H = G₁. The alternative 13.8.8(1) is the
earlier 13.8.5 branch, outside this conditional module argument.

The marked parabolic and generating seed align all maximal quotients. The
fixed generator forces uniqueness of the maximal submodule. The six-factor
strong-offender and reversed-pair argument excludes exterior-square chief
factors, and the cohomology calculation removes central factors. If the whole
module were not natural, the maximal kernel would contain an irreducible
natural-or-dual submodule. The two-factor B.4.9 splitting induction, actual
line normalizers and middle-node parabolic exclude cyclic actors. The forward
and reversed critical-pair geometry supplies the remaining inequalities and
line-valued commutator; the terminal noncyclic argument yields a contradiction.

The only representation-classification inputs are the precise universal
B.4.2/B.4.5 and two-factor B.4.9 statements. Natural heads, unique maximality,
chief factors, nonsplitting, A₁ placement, actor ranks, the fixed two-plane and
all inequalities in the new L₄ argument are derived. Relative normality,
quotient kernels and the actual ambient conjugators are retained throughout.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.960–962, PDF pp.977–979.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
open Representation.BinaryOffender
variable {H U : Type*} [Group H] [Finite H] [AddCommGroup U] [Module (ZMod 2) U]
  [FiniteDimensional (ZMod 2) U] (ρ : Representation (ZMod 2) H U)

/-- The radical and nonsplitting geometry supplies three premises of the
terminal contradiction: the actor rank bound, the quotient fixed codimension,
and the correctly conjugated fixed plane. The critical-pair and irreducible-
submodule inputs remain explicit. -/
theorem noncyclic_endgame_of_radical_axis_exclusion
    (W I : Subrepresentation ρ) (hIW : I ≤ W) (D S : Submodule (ZMod 2) U)
    (A V : Subgroup H) (hAV : A ≤ V) (hV : IsElementaryTwo V) (hA : 1 < rank A)
    (hbound : Module.finrank (ZMod 2) (U ⧸ D) ≤ rank A)
    (hIcodim : 2 ≤ Module.finrank (ZMod 2)
      (I.toSubmodule ⧸ D.comap I.toSubmodule.subtype))
    (hsym : Module.finrank (ZMod 2) (U ⧸ D) = rank A → D ≤ fixedSpace ρ A)
    (hS : Module.finrank (ZMod 2) S ≤ 1)
    (hcomm : ∀ a ∈ A, ∀ d ∈ D, ρ a d - d ∈ S)
    (eH : H ≃* BinaryLinear.GL (Fin 4 → ZMod 2))
    (eQ : (U ⧸ W.toSubmodule) ≃ₗ[ZMod 2] (Fin 4 → ZMod 2))
    (heQ : ∀ g q, eQ (W.quotientRepresentation g q) = eH g (eQ q))
    (P : Submodule (ZMod 2) (Fin 4 → ZMod 2)) (hP : Module.finrank (ZMod 2) P = 2)
    (g : H)
    (hrad : (V.map (MulAut.conj g).toMonoidHom).map eH.toMonoidHom ≤
      BinaryLinear.radical P)
    (haxis : ∀ B ≤ V, 1 < rank B → 1 < fixedCodim W.quotientRepresentation B) :
    False := by
  let Q := P.map (eH g⁻¹).toLinearMap
  have hQdim : Module.finrank (ZMod 2) Q = 2 :=
    (LinearEquiv.finrank_map_eq (eH g⁻¹) P).trans hP
  have hradQ := le_radical_of_conjugate eH P V g hrad
  let F := Q.comap eQ.toLinearMap
  have hFfix : F ≤ fixedSpace W.quotientRepresentation V := by
    intro q hq a
    apply eQ.injective
    exact (heQ a q).trans ((hradQ (Subgroup.mem_map_of_mem eH.toMonoidHom a.property)).1
      (eQ q) hq)
  have hFdim : Module.finrank (ZMod 2) F = 2 := by
    have he := (Submodule.Quotient.equiv F Q eQ
      (Submodule.map_comap_eq_of_surjective eQ.surjective Q)).finrank_eq
    have hd := F.finrank_quotient_add_finrank
    have hq := Q.finrank_quotient_add_finrank
    have hdim := eQ.finrank_eq
    omega
  have hdisplace : ∀ a ∈ V, ∀ q, W.quotientRepresentation a q - q ∈ F := by
    intro a ha q
    change eQ (W.quotientRepresentation a q - q) ∈ Q
    rw [map_sub, heQ]
    exact (hradQ (Subgroup.mem_map_of_mem eH.toMonoidHom ha)).2 (eQ q)
  have hfour : Module.finrank (ZMod 2) (U ⧸ W.toSubmodule) = 4 := by
    rw [eQ.finrank_eq]
    simp
  have hVrank := rank_le_three_of_no_noncyclic_axis W.quotientRepresentation hfour
    F hFdim V hV hFfix hdisplace haxis
  have hArank : rank A ≤ 3 :=
    (Nat.log_monotone (Subgroup.card_le_of_le hAV)).trans hVrank
  apply noncyclic_endgame_of_natural_quotient ρ W I hIW D S A hArank hbound
    hIcodim (haxis A hAV hA) hsym hS hcomm eH eQ heQ Q hQdim
  intro a ha q hq
  exact (hradQ (Subgroup.mem_map_of_mem eH.toMonoidHom (hAV ha))).1 q hq

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure

open Representation Representation.BinaryOffender Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
open ChiefFactors ChiefFactors.Alignment CriticalTransfer CriticalGeometry CriticalGeometry.Reorientation
open CriticalTransfer.PairConsequences CriticalTransfer.PairConsequences.ReversedSourceData
open Chapter2.ComponentRefinement.LieType.Binary
open FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
open LinearReduction.Parabolics
universe v
variable {G : Type v} [Group G] [Finite G]

/-- The L₄ module conclusion in the strict critical-pair branch of 13.8.25.
The action is the literal conjugation action on U_H/V₁. Earlier source
geometry and the group conclusions remain explicit, as do the precise B.4
classification and two-factor splitting inputs. Every new L₄ module deduction
is discharged, and the output identifies the whole module equivariantly. -/
theorem source_natural_module_of_strict_critical_pair
    (H K M L V V₁ V₂ V₃ : Subgroup G) (T : Sylow 2 G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    [IsElementaryAbelian 2 (Source.VH H V)]
    (d : LocalAction.NaturalSetup L T V V₁ V₃)
    (c : CriticalPair L T H V)
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SourceSpace H V₃ V₁))
    (hρ : IsSourceAction H V₃ V₁ ρ)
    (hKH : K ≤ H) (hLK : one L T V₁ ≤ K)
    (hLM : one L T V₁ ≤ M) (hTM : T ≤ M)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (hT : Chapter1.IsSylowIn 2 T H) (hKT : K ⊔ T = H)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L))
    (hfactor : one L T V₁ = plus L T V₁ ⊔ zero L)
    (hrel : ((one L T V₁).subgroupOf (H ⊓ M)).Normal)
    (hNM : normalizer (zero L : Set G) ≤ M)
    (eK : (K ⧸ pCore 2 K) ≃* PSL 4)
    (hseedIndex : V₁.relIndex V₃ = 4)
    (hirr : ∀ X : Subgroup G, V₁ ≤ X → X ≤ V₃ →
      one L T V₁ ≤ normalizer (X : Set G) → X = V₁ ∨ X = V₃)
    (hVH : V ≤ H) (hz : H ≤ centralizer (V₁ : Set G)) (hline : Nat.card V₁ = 2)
    (he : (L ⊔ T) ⊓ H = one L T V₁ ⊔ T)
    (hKγ : ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)).Normal)
    (hresγ : pResidual 2 ((K.map (MulAut.conj (c.gb : G)).toMonoidHom).subgroupOf
      (vertexGroup L T H c.gamma)) = ⊤)
    (hqsγ : IsQuasisimple (Source.starImage (vertexGroup L T H c.gamma)
      (K.map (MulAut.conj (c.gb : G)).toMonoidHom)))
    (hU : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hQ : ⁅Source.UH H V₃, Source.QH H⁆ ≤ V₁)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃)
    (hindex : V₃.relIndex V = 2) (hnorm : (L ⊔ T) ⊓ H ≤ normalizer (V : Set G))
    (hgeo : ∀ b : CriticalPair L T H V, EarlierGeometry b V₃ V₁)
    (hcore : ∀ b : CriticalPair L T H V,
      b.Vgamma ≤ (edgeGroup L T H (base L T H true) b.second).pCoreIn 2)
    (hF916 : ∀ b : CriticalPair L T H V,
      0 < rank (Source.starImage H (b.Ugamma V₃)) →
      denominatorRank V₃ V₁ b ≤ rank (Source.starImage H (b.Ugamma V₃)) →
      fixedCodim ρ (Source.starImage H (b.Ugamma V₃)) ≤
        2 * rank (Source.starImage H (b.Ugamma V₃)))
    (hD : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃)
    (hp : 0 < rank (Source.starImage H (c.Ugamma V₃)))
    (hcomp : denominatorRank V₃ V₁ c ≤ rank (Source.starImage H (c.Ugamma V₃)))
    (hrV : 1 < rank (Source.starImage H c.Vgamma))
    (hB4 : ∀ e : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace, LinearB4.{v} e)
    (hH : H = normalizer (V₁ : Set G))
    (hHC : ⁅Source.HC H V₃, Source.VH H V⁆ ≤ V₁)
    (h₂₃ : V₂ ≤ V₃) (hidx : V₁.relIndex V₂ = 2)
    (hTV₂ : (T : Subgroup G) ≤ normalizer (V₂ : Set G))
    (hinter : V ⊓ Source.UH H V₃ = V₃)
    (generation18 : ∀ b : CriticalPair L (T : Subgroup G) H V,
      ∀ F ≤ Source.UH H V₃,
      ¬ F ≤ Source.DH (Source.UH H V₃) (b.Ugamma V₃) (b.Aone V₁) →
      vertexGroup L (T : Subgroup G) H b.gamma =
        conjugateSpanBy F (vertexGroup L (T : Subgroup G) H b.gamma) ⊔
          edgeGroup L (T : Subgroup G) H b.gamma b.previous)
    (hsplit : SplittingCyclic.AxisExclusions.TwoFactorSplitting.{v, v} (Source.Hstar H))
    {E : Type v} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (τ : Representation (ZMod 2) (Source.Hstar H) E)
    (t : UpperSection H (Source.VH H V) (Source.UH H V₃) τ) :
    ∃ (eH : Source.Hstar H ≃* BinaryLinear.GL NaturalSpace)
      (eU : SourceSpace H V₃ V₁ ≃ₗ[ZMod 2] NaturalSpace),
      (∀ a u, eU (ρ a u) = eH a (eU u)) ∧
      Module.finrank (ZMod 2) (SourceSpace H V₃ V₁) = 4 := by
  obtain ⟨e, P, W, hP, hmark, hheads, hW, hu, hfactors, hatom⟩ :=
    source_chief_factors H K M L T V V₁ V₃ d c ρ hρ hKH hLK hLM hTM hK hKn hT hKT
      hcover hfactor hrel hNM eK hseedIndex hirr hVH hz hline he hKγ hresγ hqsγ hU hQ
      hnoncentral hindex hnorm hgeo hcore hF916 hD hp hcomp hrV hB4
  have hn : IsNatural ρ e := by
    by_contra hn
    obtain ⟨hW0, N, hN, hNW⟩ := hatom hn
    obtain ⟨eQ, heQ⟩ := hheads W hW
    let s := sourceConjugationSection H V₃ V₁ ρ hρ
      (conjugateSpanBy_le_self (d.seed_le.trans hVH)) hz
      (d.line_le_seed.trans (le_conjugateSpanBy V₃ H))
    have hTH := (Chapter1.isSylowIn_iff.mp hT).2.1
    have ht := (Chapter1.isSylowIn_iff.mp hT).1
    have hPH : one L T V₁ ⊔ (T : Subgroup G) ≤ H := sup_le (hLK.trans hKH) hTH
    have hseedNorm : one L T V₁ ⊔ (T : Subgroup G) ≤ normalizer (V₃ : Set G) := by
      apply sup_le _ d.seed_stable
      rw [hfactor]
      exact sup_le d.plus_normalizes_seed
        ((d.zero_centralizes.trans (centralizer_le d.seed_le)).trans (Subgroup.centralizer_le_normalizer _))
    have hseedLine : V₁ < V₃ := lt_of_le_of_ne d.line_le_seed (by
      intro heq
      rw [heq, relIndex_self] at hseedIndex
      contradiction)
    let seed := Alignment.sourceSeedOfEarlier H V₃ V₁ ρ hρ (one L T V₁ ⊔ (T : Subgroup G))
      T hPH le_sup_right ht hseedNorm hseedLine
      (fun X hx hy hn => hirr X hx hy (le_sup_left.trans hn)) hseedIndex
    have hstable : ∀ a : Source.starImage H (one L T V₁ ⊔ (T : Subgroup G)),
        ∀ v ∈ s.image V₃, ρ a v ∈ s.image V₃ := by
      intro a v hv
      exact seed.space.apply_mem_toSubmodule a hv
    have hseedIrr : IsAtom (⟨s.image V₃, hstable⟩ : Subrepresentation
        (ρ.comp (Source.starImage H (one L T V₁ ⊔ (T : Subgroup G))).subtype)) := seed.irreducible
    have hseedDim : Module.finrank (ZMod 2) (s.image V₃) = 2 := seed.dim_two
    obtain ⟨I, hZI, hIU, hNI⟩ := AssemblyInputs.preimage_submodule s N
    let S : SourceData L (T : Subgroup G) H V V₃ V₁ ρ := {
      sectionModel := s
      normalizer_line := hH
      line_card := hline
      seed_le := d.seed_le
      V_le := hVH
      flag_index := hindex
      edge_normalizes := hnorm
      noncentral := hnoncentral
      centralizer_bound := hHC
      L₀ := zero L
      L₁ := one L T V₁
      edge_eq := he
      L₀_le := by rw [hfactor]; exact le_sup_right
      cubic := d.zero_core_card
      fixes_seed := d.zero_seed_commutator
      two_group := ht
      seed_stable := hstable
      seed_irreducible := hseedIrr
      seed_dim := hseedDim
      eH := e
      W := W
      maximal := hW
      nonzero := hW0
      unique_maximal := hu
      head := eQ
      head_equivariant := heQ
      chief_factors := hfactors
      splitting := hsplit
      N := N
      irreducible := hN
      submodule_le := hNW
      I := I
      line_le_I := hZI
      I_le := hIU
      image_I := hNI }
    have hfaith := S.faithful
    have hγH : c.Ugamma V₃ ≤ H :=
      (map_mono (conjugateSpanBy_mono d.seed_le le_rfl)).trans (hgeo c).Vgamma_H
    have hcritical : Nat.log 2 ((Source.DH (Source.UH H V₃) (c.Ugamma V₃)
        (c.Aone V₁)).relIndex (Source.UH H V₃)) ≤
        Nat.log 2 ((Source.Dgamma (c.Ugamma V₃) (Source.UH H V₃) V₁).relIndex (c.Ugamma V₃)) := by
      rw [s.Dgamma_relIndex _ hγH hfaith]
      exact hcomp
    have hmarked := AssemblyInputs.parabolic_eq_headPlane S P hmark
    obtain ⟨g, hb, hi, hs, hl, hc, hAB, hB, hA, hp₂, hr, ha⟩ :=
      AssemblyInputs.source_endgame_inputs T S c hgeo hcore generation18 hp hrV (hF916 c hp hcomp)
        hcritical V₂ h₂₃ hidx hTV₂ hmarked hinter τ t
    exact noncyclic_endgame_of_radical_axis_exclusion ρ S.W S.N S.submodule_le
      (s.image (Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁)))
      (s.image (c.Aone V₁)) (Source.starImage H (c.Ugamma V₃)) (Source.starImage H c.Vgamma)
      hAB hB hA hb hi hs hl hc S.eH S.head S.head_equivariant S.plane hp₂ g hr ha
  obtain ⟨eU, heU⟩ := hn
  refine ⟨e, eU, heU, ?_⟩
  rw [eU.finrank_eq]
  simp [NaturalSpace]

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
