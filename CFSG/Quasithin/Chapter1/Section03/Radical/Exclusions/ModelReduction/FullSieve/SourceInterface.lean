module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.SourceInterface.MSPairs

/-!
# Full source interface for C.2.7 and the radical-sieve specialization

`Conclusion` contains both local conclusions and all eight alternatives of
C.2.7, including each of the four chi-block cases. `Source` is the universally
quantified implication from the genuine C.2.3 setup and component hypotheses.
It is an explicit theorem parameter, not an axiom or a proved C.2.7 theorem.
The proof below specializes that implication to the radical construction and
then forgets the geometric and module information not consumed by the sieve.

Block subnormality is relative to H; block types describe the actual carrier
K, and every starred subgroup is taken in KR/C_KR(Ω₁(Z(O₂(KR)))). No normality
in the larger ambient G or interchange of the core and star quotients occurs.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, C.2.7,
printed pp.145–147; C.1.34, pp.136–137; proof of 1.3.8, p.514.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Subgroup ChapterC
open scoped Pointwise
universe u
variable {G : Type u} [Group G]

/-- The natural alternating module, compatibly identified with the actual
star component and with conjugation on the block module. -/
structure AlternatingComponentModel (K R : Subgroup G) (n : ℕ) where
  groupIso : starImage K R K ≃* alternatingGroup (Fin n)
  moduleIso : BlockModule K ≃* Multiplicative (BinaryPermutation.natural (Fin n))
  compatible : ∀ (k : K) (v : blockU K),
    Multiplicative.toAdd (moduleIso (QuotientGroup.mk' (blockFixed K)
      (blockConjugate K k v))) =
      BinaryPermutation.naturalRepresentation (Fin n) (groupIso (toStarImage K R k)).val
        (Multiplicative.toAdd (moduleIso (QuotientGroup.mk' (blockFixed K) v)))

/-- The whole symmetric extension, with its actual alternating component
and the compatible natural module. -/
structure SymmetricStarModel (K R : Subgroup G) (n : ℕ) where
  groupIso : StarQuotient K R ≃* Equiv.Perm (Fin n)
  component : (starImage K R K).map groupIso.toMonoidHom = alternatingGroup (Fin n)
  moduleIso : BlockModule K ≃* Multiplicative (BinaryPermutation.natural (Fin n))
  compatible : ∀ (g : (K ⊔ R : Subgroup G)) (v w : blockU K),
    ((w : K) : G) = (g : G) * ((v : K) : G) * (g : G)⁻¹ →
      Multiplicative.toAdd (moduleIso (QuotientGroup.mk' (blockFixed K) w)) =
        BinaryPermutation.naturalRepresentation (Fin n)
          (groupIso (QuotientGroup.mk' (starKernel K R) g))
          (Multiplicative.toAdd (moduleIso (QuotientGroup.mk' (blockFixed K) v)))

/-- Exactly the four subcases of C.2.7(3)(a). -/
inductive ChiAlternative (K R MH : Subgroup G) : Prop
  | binary (n : ℕ) (block : IsL2EvenBlock K n)
      (sylow : IsSylowIn 2 (starImage K R (Stellmacher.elementaryAbelianMaxJ R))
        (starImage K R K))
      (borel : IsRankOneBorel (starImage K R K) (starM K R MH))
  | five (block : IsAlternatingBlock K 5) (sylow : IsSylowIn 2 R (K ⊔ R))
      (extension : Nonempty (SymmetricStarModel K R 5))
      (borel : IsRankOneBorel (starImage K R K) (starM K R MH))
  | sevenDihedral (block : IsAlternatingBlock K 7)
      (radical : Nonempty (starImage K R R ≃* DihedralGroup 4))
      (extension : ∃ e : SymmetricStarModel K R 7,
        ∃ d : Partition 7 2 ![4, 3],
          (starM K R MH).map e.groupIso.toMonoidHom =
            alternatingGroup (Fin 7) ⊓ d.stabilizer)
  | sevenElementary (block : IsAlternatingBlock K 7)
      (radical : Nonempty (starImage K R R ≃* Multiplicative (Fin 3 → ZMod 2)))
      (extension : ∃ e : SymmetricStarModel K R 7,
        ∃ d : Partition 7 4 ![2, 2, 2, 1],
          (starM K R MH).map e.groupIso.toMonoidHom =
            alternatingGroup (Fin 7) ⊓ d.stabilizer)

/-- In (b), the generator of R* acts by an actual transposition on the
identified alternating component. The equivalence of the two conjugation
equations fixes the action, not just the isomorphism type of R*. -/
def TranspositionAction (K R : Subgroup G) (n : ℕ) : Prop :=
  ∃ e : AlternatingComponentModel K R n,
    ∃ (r : StarQuotient K R) (t : Equiv.Perm (Fin n)),
      orderOf r = 2 ∧ starImage K R R = closure {r} ∧ t.IsSwap ∧
      ∀ k k' : starImage K R K,
        (k' : StarQuotient K R) = r * (k : StarQuotient K R) * r⁻¹ ↔
          (e.groupIso k' : Equiv.Perm (Fin n)) =
            t * (e.groupIso k : Equiv.Perm (Fin n)) * t⁻¹

/-- In (c), U(K) is the actual three-dimensional F₄-space, and M_K is
the stabilizer of a plane under its conjugation action. -/
def AhatPlaneStabilizer (K MH : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
    ∃ (e : blockU K ≃* Multiplicative (Fin 3 → F))
      (rho : K →* ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)))
      (W : Submodule F (Fin 3 → F)),
      Module.finrank F W = 2 ∧
      (∀ (k : K) (v : blockU K),
        Multiplicative.toAdd (e (blockConjugate K k v)) =
          rho k (Multiplicative.toAdd (e v))) ∧
      (MH ⊓ K).subgroupOf K =
        (MulAction.stabilizer ((Fin 3 → F) ≃ₗ[F] (Fin 3 → F)) W).comap rho

/-- All eight alternatives, with subnormality in H in every block case. -/
inductive Alternatives (κ : GroupClass.{u}) (H K R MH : Subgroup G) : Prop
  | chi (block : IsBlock (K.subgroupOf H)) (chi : IsChiBlock K)
      (cases : ChiAlternative K R MH)
  | alternating (n : ℕ) (lower : 5 ≤ n) (upper : n ≤ 8)
      (block : IsBlock (K.subgroupOf H)) (model : IsAlternatingBlock K n)
      (action : TranspositionAction K R n)
      (centralizer : starM K R MH =
        starImage K R K ⊓ Subgroup.centralizer (starImage K R R : Set (StarQuotient K R)))
  | ahatSix (block : IsBlock (K.subgroupOf H)) (model : IsExceptionalAhat6Block K)
      (index : ((MH ⊓ K).subgroupOf K).index = 15)
      (stabilizer : AhatPlaneStabilizer K MH)
  | exceptionalSeven (block : IsBlock (K.subgroupOf H)) (model : IsExceptionalA7Block K)
      (index : ((MH ⊓ K).subgroupOf K).index = 35)
  | rankTwo (block : IsBlock (K.subgroupOf H))
      (cases : (IsAlternatingBlock K 6 ∧
        IsA6MaximalParabolic ((starM K R MH).subgroupOf (starImage K R K))) ∨
        (IsSp4FourBlock K ∧
        IsSp4FourMaximalParabolic ((starM K R MH).subgroupOf (starImage K R K))))
  | binaryG2 (block : IsBlock (K.subgroupOf H)) (model : IsG2TwoBlock K)
      (extension : ∃ e : StarQuotient K R ≃* Atlas.G2.Model (ZMod 2),
        IsG2MaximalParabolic ((starM K R MH ⊔ starImage K R R).map e.toMonoidHom))
  | linearThree (n : ℕ) (F : Type) [field : Field F] [finite : Finite F]
      (positive : 1 ≤ n) (field_card : Nat.card F = 2 ^ n)
      (parabolic : IsLinearMaximalParabolic
        ((starM K R MH).subgroupOf (starImage K R K)) 3 F)
      (ms : MSDescription κ K R n F)
  | binaryLinear (n : ℕ) (degree : n = 4 ∨ n = 5)
      (parabolic : IsBinaryPositiveRankParabolic
        ((starM K R MH).subgroupOf (starImage K R K)) n)

/-- The complete conclusion of C.2.7. The eight-case alternative is not
replaced by its model projection. -/
structure Conclusion (κ : GroupClass.{u}) (H K R MH : Subgroup G) : Prop where
  kernel : KernelConclusion K R
  offenders : OffenderConclusion K R
  alternatives : Alternatives κ H K R MH

/-- The exact universal source implication for finite H, authorized as a
parameter for this deduction. Proving C.2.7 remains a separate source-theorem
obligation; the surrounding ambient carrier need not itself be finite. -/
def Source (κ : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ (H R MH K : Subgroup G), Finite H →
    Input κ H R MH K → Conclusion κ H K R MH

/-- Forget the geometric clauses only after obtaining a full alternative. -/
theorem Alternatives.modelCases {κ : GroupClass.{u}} {H K R MH : Subgroup G}
    (h : Alternatives κ H K R MH) : ModelCases H K R := by
  cases h with
  | chi hb hc ha =>
    cases ha with
    | binary n hm _ _ => exact .binary hb ⟨n, hm⟩
    | five hm _ _ _ => exact .alternating 5 (by decide) (by decide) hb hm
    | sevenDihedral hm _ _ => exact .alternating 7 (by decide) (by decide) hb hm
    | sevenElementary hm _ _ => exact .alternating 7 (by decide) (by decide) hb hm
  | alternating n hn hu hb hm _ _ => exact .alternating n hn hu hb hm
  | ahatSix _ hm _ _ => exact .ahatSix hm
  | exceptionalSeven _ hm _ => exact .exceptionalSeven hm
  | rankTwo hb ha =>
    rcases ha with ⟨hm, _⟩ | ⟨hm, _⟩
    · exact .alternating 6 (by decide) (by decide) hb hm
    · exact .symplecticFour hm
  | binaryG2 _ hm _ => exact .binaryG2 hm.quotient_model
  | linearThree n F hn hF hp _ =>
    obtain ⟨e, _⟩ := hp
    exact .linearThree ⟨n, hn, F, inferInstance, inferInstance, hF, ⟨e⟩⟩
  | binaryLinear n hn hp => exact .binaryLinear n hn hp.model

/-- The full C.2.7 implication gives the exact kernel bound and model
projection consumed by the radical sieve. All hypotheses are supplied by
the actual component construction, including relative outside-ness and
normalization by R=O₂(XT). -/
theorem specialize [Finite G] {κ : GroupClass.{u}} {p : ℕ}
    {T X P M H₀ K : Subgroup G} (source : Source κ G)
    (h : PushingUpComponent κ p T X P M H₀ K) :
    StarKernelBound K ((X ⊔ T).pCoreIn 2) ∧
      ModelCases H₀ K ((X ⊔ T).pCoreIn 2) := by
  have hs := source H₀ ((X ⊔ T).pCoreIn 2) (H₀ ⊓ M) K inferInstance
    (input_of_pushingUpComponent h)
  exact ⟨hs.kernel.upper, hs.alternatives.modelCases⟩

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
