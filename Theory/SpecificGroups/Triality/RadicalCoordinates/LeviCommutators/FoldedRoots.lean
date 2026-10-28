module

public import Theory.SpecificGroups.Triality.RadicalCoordinates.FixedPoints

/-!
# The six positive folded root groups in genuine triality

The three short roots are the ordered triples (0,1,2), (4,5,6), and
(7,8,9), with parameters t, F(t), F²(t). The three long roots are the
singleton positions 3, 10, and 11, with parameters in the actual fixed field.
The published fixed coordinates put these elements in the elementary group
and retain their precise marking after the central quotient. Factoring the
ordered normal form proves generation of both radical root products by the
five surviving folded root groups.

Source: GLS3 §§2.4 and 2.6 (`refs/KGroup/GLS3/chapter2.tex`), for the
triality branch of Aschbacher–Smith F.1.12(II), printed pp.263–264.
-/

@[expose] public section
noncomputable section
namespace Triality.Standard.RadicalCoordinates.LeviCommutators
open Parabolics PositiveCoordinates

def shortPosition : Fin 3 → Fin 3 → Fin 12 :=
  ![![0, 1, 2], ![4, 5, 6], ![7, 8, 9]]

def longPosition : Fin 3 → Fin 12 := ![3, 10, 11]

def shortSplit (P : Parameters) (i : Fin 3) (t : ExtensionField P) : SplitGroup P :=
  curve P (shortPosition i 0) t *
    curve P (shortPosition i 1) (fieldFrobenius P t) *
      curve P (shortPosition i 2) (fieldFrobenius P (fieldFrobenius P t))

def longSplit (P : Parameters) (i : Fin 3) (t : fixedField P) : SplitGroup P :=
  curve P (longPosition i) t.val

theorem orderedProduct_expand_fixed (P : Parameters) (hp : P.prime = 2)
    (v : OrbitParameters P) : orderedProduct P (expand P v) ∈ fixedSubgroup P := by
  obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
  rw [mem_fixedSubgroup, graphField_orderedProduct_binary, expand_fixed]

/-- Lift a fixed root product using its proved elementary membership.
The value is explicit to avoid unfolding the normal-form equivalence at each use. -/
def rootElement (P : Parameters) (hp : P.prime = 2) (a : Node)
    (v : RootOrbitParameters P a) : ElementaryGroup P :=
  ⟨⟨orderedProduct P (expand P (extendOrbit P a v)),
      orderedProduct_expand_fixed P hp _⟩,
    fixedRootSubgroup_le_elementary P hp a
      (orderedProduct_mem_rootSubgroup P a
        ⟨expand P (extendOrbit P a v), expand_extendOrbit_supported P a v⟩)⟩

theorem rootElement_val (P : Parameters) (hp : P.prime = 2) (a : Node)
    (v : RootOrbitParameters P a) :
    elementaryInclusion P (rootElement P hp a v) =
      orderedProduct P (expand P (extendOrbit P a v)) := rfl

def shortElementary (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (t : ExtensionField P) : ElementaryGroup P :=
  rootElement P hp .central (Function.update 0 i t, 0)

def longElementary (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (t : fixedField P) : ElementaryGroup P :=
  rootElement P hp .arms (0, Function.update 0 i t)

theorem shortElementary_val (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : ExtensionField P) :
    elementaryInclusion P (shortElementary P hp i t) = shortSplit P i t := by
  change orderedProduct P (expand P (extendOrbit P .central
    (Function.update 0 i t, 0))) = shortSplit P i t
  fin_cases i <;>
    simp [shortSplit, shortPosition, orderedProduct, expand, extendOrbit,
      List.ofFn_succ, -fieldFrobenius_apply, mul_assoc]

theorem longElementary_val (P : Parameters) (hp : P.prime = 2)
    (i : Fin 3) (t : fixedField P) :
    elementaryInclusion P (longElementary P hp i t) = longSplit P i t := by
  change orderedProduct P (expand P (extendOrbit P .arms
    (0, Function.update 0 i t))) = longSplit P i t
  fin_cases i <;>
    simp [longSplit, longPosition, orderedProduct, expand, extendOrbit,
      List.ofFn_succ, -fieldFrobenius_apply]

def short (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (t : ExtensionField P) : Carrier P := toCarrier P (shortElementary P hp i t)

def long (P : Parameters) (hp : P.prime = 2) (i : Fin 3)
    (t : fixedField P) : Carrier P := toCarrier P (longElementary P hp i t)

def shortSupported : Node → Fin 3 → Prop
  | .arms, i => i ≠ 0
  | .central, _ => True

def longSupported : Node → Fin 3 → Prop
  | .arms, _ => True
  | .central, i => i ≠ 0

theorem short_mem (P : Parameters) (hp : P.prime = 2) (a : Node)
    (i : Fin 3) (hi : shortSupported a i) (t : ExtensionField P) :
    short P hp i t ∈ descendSubgroup P (rootSubgroup P a) := by
  refine ⟨shortElementary P hp i t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ rootSubgroup P a
  rw [shortElementary_val, shortSplit]
  have hs (j : Fin 3) : rootSupport a (shortPosition i j) := by
    cases a <;> fin_cases i <;> fin_cases j <;>
      simp_all [shortSupported, rootSupport, shortPosition]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _
    (curve_mem_rootSubgroup P a _ (hs 0) _)
    (curve_mem_rootSubgroup P a _ (hs 1) _))
    (curve_mem_rootSubgroup P a _ (hs 2) _)

theorem long_mem (P : Parameters) (hp : P.prime = 2) (a : Node)
    (i : Fin 3) (hi : longSupported a i) (t : fixedField P) :
    long P hp i t ∈ descendSubgroup P (rootSubgroup P a) := by
  refine ⟨longElementary P hp i t, ?_, rfl⟩
  change elementaryInclusion P _ ∈ rootSubgroup P a
  rw [longElementary_val, longSplit]
  apply curve_mem_rootSubgroup
  cases a <;> fin_cases i <;> simp_all [longSupported, rootSupport, longPosition]

theorem elementaryInclusion_injective (P : Parameters) :
    Function.Injective (elementaryInclusion P) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

@[simp] theorem short_zero (P : Parameters) (hp : P.prime = 2) (i : Fin 3) :
    short P hp i 0 = 1 := by
  have h : shortElementary P hp i 0 = 1 := by
    apply elementaryInclusion_injective P
    simp [shortElementary_val, shortSplit, -fieldFrobenius_apply]
  simp [short, h]

@[simp] theorem long_zero (P : Parameters) (hp : P.prime = 2) (i : Fin 3) :
    long P hp i 0 = 1 := by
  have h : longElementary P hp i 0 = 1 := by
    apply elementaryInclusion_injective P
    simp [longElementary_val, longSplit]
  simp [long, h]

/-- The fixed positive normal form is a product in the six folded root groups,
in the original order; no commuting or collection convention is changed. -/
theorem orderedProduct_expand (P : Parameters) (v : OrbitParameters P) :
    orderedProduct P (expand P v) =
      shortSplit P 0 (v.1 0) * longSplit P 0 (v.2 0) *
        shortSplit P 1 (v.1 1) * shortSplit P 2 (v.1 2) *
          longSplit P 1 (v.2 1) * longSplit P 2 (v.2 2) := by
  simp [orderedProduct, expand, shortSplit, longSplit, shortPosition, longPosition,
    List.ofFn_succ, mul_assoc]

theorem rootElement_factorization (P : Parameters) (hp : P.prime = 2) (a : Node)
    (v : RootOrbitParameters P a) :
    toCarrier P (rootElement P hp a v) =
      short P hp 0 ((extendOrbit P a v).1 0) *
        long P hp 0 ((extendOrbit P a v).2 0) *
        short P hp 1 ((extendOrbit P a v).1 1) *
        short P hp 2 ((extendOrbit P a v).1 2) *
        long P hp 1 ((extendOrbit P a v).2 1) *
        long P hp 2 ((extendOrbit P a v).2 2) := by
  simp only [short, long, ← map_mul]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul, shortElementary_val, longElementary_val, rootElement_val]
  exact orderedProduct_expand P _

/-- Fixed supported split elements have the five independent orbit parameters. -/
theorem exists_orbitParameters (P : Parameters) (hp : P.prime = 2) (a : Node)
    (g : SplitGroup P) (hg : g ∈ rootSubgroup P a) (hfixed : g ∈ fixedSubgroup P) :
    ∃ v : RootOrbitParameters P a,
      orderedProduct P (expand P (extendOrbit P a v)) = g := by
  obtain ⟨v, hv⟩ := (mem_rootSubgroup_iff P hp a g).mp hg
  have hfix : twist P v.val = v.val := by
    have hinj : Function.Injective (orderedProduct P) := by
      obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
      exact orderedProduct_injective_binary n hn
    have htwist : graphFieldAutomorphism P (orderedProduct P v.val) =
        orderedProduct P (twist P v.val) := by
      obtain ⟨n, hn, rfl⟩ := (exists_binaryParameters_iff P).mpr hp
      exact graphField_orderedProduct_binary n hn v.val
    apply hinj
    rw [← htwist, hv]
    exact hfixed
  let w : FixedSupportedCoordinates P a := ⟨⟨v.val, hfix⟩, v.property⟩
  let u := (rootOrbitEquiv P a).symm w
  have hu : expand P (extendOrbit P a u) = v.val :=
    congrArg (fun z => z.val.val) ((rootOrbitEquiv P a).apply_symm_apply w)
  exact ⟨u, (congrArg (orderedProduct P) hu).trans hv⟩

private theorem map_comap_exists_of_parameters {G E Q A : Type*}
    [Group G] [Group E] [Group Q] (inc : E →* G) (π : E →* Q)
    (U F : Subgroup G) (r : A → E) (s : A → G) (hi : Function.Injective inc)
    (hr : ∀ v, inc (r v) = s v) (hf : ∀ y, inc y ∈ F)
    (hs : ∀ g, g ∈ U → g ∈ F → ∃ v, s v = g)
    (g : Q) (hg : g ∈ (U.comap inc).map π) : ∃ v, π (r v) = g := by
  obtain ⟨y, hy, hyg⟩ := hg
  obtain ⟨v, hv⟩ := hs (inc y) hy (hf y)
  refine ⟨v, (congrArg π (hi ?_)).trans hyg⟩
  exact (hr v).trans hv

/-- Every descended root-product element has the published fixed parameters. -/
theorem exists_rootElement (P : Parameters) (hp : P.prime = 2) (a : Node)
    {g : Carrier P} (hg : g ∈ descendSubgroup P (rootSubgroup P a)) :
    ∃ v : RootOrbitParameters P a, toCarrier P (rootElement P hp a v) = g := by
  exact map_comap_exists_of_parameters (elementaryInclusion P) (toCarrier P)
    (rootSubgroup P a) (fixedSubgroup P) (rootElement P hp a)
    (fun v => orderedProduct P (expand P (extendOrbit P a v)))
    (elementaryInclusion_injective P) (rootElement_val P hp a)
    (fun y => y.val.property) (exists_orbitParameters P hp a) g hg

/-- The surviving five folded root groups generate the actual descended root
product. This is proved from the fixed normal form, not assumed generation. -/
theorem descendedRoot_le_of_folded (P : Parameters) (hp : P.prime = 2) (a : Node)
    (H : Subgroup (Carrier P))
    (hs : ∀ i, shortSupported a i → ∀ t, short P hp i t ∈ H)
    (hl : ∀ i, longSupported a i → ∀ t, long P hp i t ∈ H) :
    descendSubgroup P (rootSubgroup P a) ≤ H := by
  intro g hg
  obtain ⟨v, rfl⟩ := exists_rootElement P hp a hg
  rw [rootElement_factorization]
  have hshort (i : Fin 3) : short P hp i ((extendOrbit P a v).1 i) ∈ H := by
    by_cases hi : shortSupported a i
    · exact hs i hi _
    · have he : (extendOrbit P a v).1 i = 0 := by
        cases a <;> fin_cases i <;> simp_all [shortSupported, extendOrbit]
      rw [he, short_zero]
      exact H.one_mem
  have hlong (i : Fin 3) : long P hp i ((extendOrbit P a v).2 i) ∈ H := by
    by_cases hi : longSupported a i
    · exact hl i hi _
    · have he : (extendOrbit P a v).2 i = 0 := by
        cases a <;> fin_cases i <;> simp_all [longSupported, extendOrbit]
      rw [he, long_zero]
      exact H.one_mem
  exact H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem
    (hshort 0) (hlong 0)) (hshort 1)) (hshort 2)) (hlong 1)) (hlong 2)

end Triality.Standard.RadicalCoordinates.LeviCommutators
