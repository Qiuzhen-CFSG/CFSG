module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.FixedLines
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ParabolicDegrees
public import Theory.Representation.CosetOrbitQuotient
public import Theory.GroupTheory.ConjugateSpanSupplement

/-!
# Permutation quotients of the original fixed-line orbits

The two distinct fixed lines have order two and span Ω₁Z(T). Each
nonidentity generator is moved by the opposite vertex. Its conjugate span
is elementary abelian, has dimension greater than one, and is an explicit
equivariant quotient of the permutation module on the original cosets.
The dimension is bounded by the corresponding parabolic index.

For the actual nonsolvable component X=KT, T fixes both lines and
normalizes K. Thus removing T does not enlarge either line orbit, and
the full omega module is the sum of their K-orbits. No direct-sum claim
is made: the indecomposable permutation-core case remains possible.

These are the original module inputs on printed p.901 of Aschbacher–Smith
13.4.7. Structural1222 and the preceding 13.3.2 implication retain their
existing producers and final discharge with this assembly. The module
classification, Thompson normality and overgroup supplement remain required;
these results do not construct PlaneAmalgamSource1347.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugateSpan_sup_seed (F₁ F₂ H : Subgroup G) :
    conjugateSpanBy (F₁ ⊔ F₂) H = conjugateSpanBy F₁ H ⊔ conjugateSpanBy F₂ H := by
  apply le_antisymm
  · apply conjugateSpanBy_le (sup_le_sup (le_conjugateSpanBy F₁ H)
      (le_conjugateSpanBy F₂ H))
    intro h hh
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup,
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy F₁ H hh),
      mem_normalizer_iff_map_conj_eq.mp (le_normalizer_conjugateSpanBy F₂ H hh)]
  · exact sup_le (conjugateSpanBy_mono le_sup_left le_rfl)
      (conjugateSpanBy_mono le_sup_right le_rfl)

omit [Finite G] in
/-- The source omega module is the sum of the actual orbits of the two fixed lines. -/
theorem pair_fixed_line_spans {T : Sylow 2 G} (A B K : Subgroup G)
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hgen : A ⊔ B = K ⊔ (T : Subgroup G))
    (hsplit : let Z := omegaOneCenterAmbient (T : Subgroup G)
      (Z ⊓ centralizer (A : Set G)) ⊔ (Z ⊓ centralizer (B : Set G)) = Z) :
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let F₁ := Z ⊓ centralizer (A : Set G)
    let F₂ := Z ⊓ centralizer (B : Set G)
    conjugateSpanBy Z (A ⊔ B) = conjugateSpanBy F₁ K ⊔ conjugateSpanBy F₂ K := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  have fixed (P : Subgroup G) : (T : Subgroup G) ≤
      normalizer (Z ⊓ centralizer (P : Set G) : Set G) := by
    apply le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    exact le_centralizer_iff.mp (inf_le_left.trans (by
      intro z hz
      exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2))
  dsimp only
  conv_lhs => rw [←hsplit]
  rw [conjugateSpan_sup_seed,hgen,
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (fixed A) hTK,
    conjugateSpanBy_sup_of_normalizes_seed _ _ _ (fixed B) hTK]
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The second fixed line supplies an actual moved generator and the literal
coset permutation quotient of its orbit module. The opposite orientation
follows by interchanging the two original vertices. -/
theorem original_pair_fixed_line_permutation_quotient
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (L : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂) :
    let X := A ⊔ B
    let F := omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)
    let U := conjugateSpanBy F X
    ∃ he : IsElementaryAbelian 2 U,
      let := he
      let actor := U.normalizerMonoidHom.comp
        (inclusion (le_normalizer_conjugateSpanBy F X))
      let ρ := Representation.elementaryRepresentation (p := 2) actor
      1 < Module.finrank (ZMod 2) (Additive U) ∧
      Module.finrank (ZMod 2) (Additive U) ≤ B.relIndex X ∧
      ∃ v : F, v ≠ 1 ∧ v.val ∉ centralizer (A : Set G) ∧
      ∃ f : ((X ⧸ B.subgroupOf X) →₀ ZMod 2) →ₗ[ZMod 2] Additive U,
        Function.Surjective f ∧
        (∀ g : X, f (Finsupp.single (QuotientGroup.mk g) 1) =
          ρ g (Additive.ofMul (inclusion (le_conjugateSpanBy F X) v))) ∧
        (∀ (g : X) x, f (Finsupp.lmapDomain (ZMod 2) (ZMod 2)
          (fun q : X ⧸ B.subgroupOf X => g • q) x) = ρ g (f x)) := by
  let X := A ⊔ B
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (B : Set G)
  let W := conjugateSpanBy Z X
  let U := conjugateSpanBy F X
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  obtain ⟨_,_,hF,hi,_,_⟩ := original_pair_fixed_lines h structural D m hout
    hindexL hindexA hindexB hd
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    (hTA.trans le_sup_left) ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hr := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  let : IsElementaryAbelian 2 (W.subgroupOf X) := hr.elementary
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hWX).symm.toMonoidHom (subgroupOfEquivOfLe hWX).symm.injective
  let he : IsElementaryAbelian 2 U := IsElementaryAbelian.of_injective
    (inclusion (conjugateSpanBy_mono (show F ≤ Z from inf_le_left) le_rfl))
    (inclusion_injective _)
  obtain ⟨v,hv,_⟩ := (Nat.card_eq_two_iff' (1 : F)).mp hF
  have hmove : v.val ∉ centralizer (A : Set G) := by
    intro hc
    have hvb : v.val ∈ (⊥ : Subgroup G) := hi ▸ ⟨⟨v.property.1,hc⟩,v.property⟩
    exact hv (Subtype.ext hvb)
  let := he
  have hlower := Representation.one_lt_finrank_conjugateLine F X hF (by
    intro hh
    exact hmove (centralizer_le (show A ≤ X from le_sup_left) (hh v.property)))
  obtain ⟨f,hf,hm,heq⟩ :=
    Representation.exists_conjugateLine_coset_map F X B inf_le_right hF v hv
  have hupper : Module.finrank (ZMod 2) (Additive U) ≤ B.relIndex X := by
    let := Fintype.ofFinite (X ⧸ B.subgroupOf X)
    have hh := LinearMap.finrank_le_finrank_of_surjective hf
    simpa only [Module.finrank_finsupp_self,relIndex,index_eq_card,Nat.card_eq_fintype_card] using hh
  exact ⟨he,hlower,hupper,v,hv,hmove,f,hf,hm,heq⟩
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Section03.Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The whole original omega module is the sum of the two component orbits.
The component and both fixed lines are those constructed from the original pair. -/
theorem original_pair_component_fixed_line_spans
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hout : ¬ A ⊔ B ≤ normalizer (L : Set G))
    (hindexL : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (L : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (A : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : ((omegaOneCenterAmbient (T : Subgroup G)) ⊓
      centralizer (B : Set G)).relIndex (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hres : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      (primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
        (primeToResidual 3 C₂).map C₂.subtype = K₂)
    (h1332 : Source1332OneTwo T)
    (K : Subgroup (A ⊔ B : Subgroup G)) (hK : K.IsCComponent) :
    let X := A ⊔ B
    let C := K.map X.subtype
    let Z := omegaOneCenterAmbient (T : Subgroup G)
    let F₁ := Z ⊓ centralizer (A : Set G)
    let F₂ := Z ⊓ centralizer (B : Set G)
    conjugateSpanBy Z X = conjugateSpanBy F₁ C ⊔ conjugateSpanBy F₂ C := by
  have hd := pair_fixed_subgroups_ne hTA hTB eA eB hne hres
  have hs := (original_pair_fixed_lines h structural D m hout
    hindexL hindexA hindexB hd).2.2.2.2.1
  have hTC := (original_pair_component_geometry h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2.2.2.1
  have hg := (original_pair_component_is_residual h₀ D m h1332
    hTA hTB eA eB hne hindexA hindexB K hK).2
  exact pair_fixed_line_spans A B (K.map (A ⊔ B).subtype) hTC hg hs
end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
