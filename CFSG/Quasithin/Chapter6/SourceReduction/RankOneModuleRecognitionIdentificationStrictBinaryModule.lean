module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionIdentificationStrictBinarySetup
public import CFSG.Quasithin.ChapterG.Section02.Binary.CoreIntersection
public import Theory.Representation.BinaryConjugationSection.FixedMoving

/-!
# The natural crossing module and its fixed-vector bound

The genuine G.2.3 application gives I = L_S U, P = WX, and the elementary
section P/E with its natural S₃ tensor model. Its complementary W/E and X/E
are retained under literal quotient coordinates. For every u in U outside
W, the displacement maps X/E onto W/E and has kernel W/E in P/E.

These coordinates identify X ∩ O₂(H) with E. They also show that an actor
x in X fixing a vector u outside W modulo ⟨z⟩ lies in E. This is the
preliminary fixed-vector calculation in 6.2.17; the further passage to
U/Z(U), rank identity and strict contradiction remain with this task.

Source: Aschbacher--Smith, 6.2.17, printed pp.689--690, using G.2.3.
The Chapter12 StrictBinaryModule application retains the whole reduced
layer. LocalAnalysis is discharged by
qt-d-1222-rankone-recognition-identification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement Pointwise TensorProduct
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {κ : GroupClass} {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ} {z : G}

/-- The G.2 core and its two factors are the actual crossing centralizers. -/
theorem LocalAnalysis.strict_binary_crossing_identifications
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    let D := strictBinarySetup (T : Subgroup G) L R z
    D.S₂ d = strictCrossingIntersection (T : Subgroup G) L R z d ∧
    D.S d = D.I d ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) ∧
    D.W d = sourceClosure (T : Subgroup G) L R z ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) ∧
    ChapterG.Section02.Setup.conjugate (D.W d) d = strictCrossingGroup (T : Subgroup G) L R z d := by
  let D := strictBinarySetup (T : Subgroup G) L R z
  have h := A.strict_binary_hypothesis h611 hnatural hz horder hTH
  let b := A.strict_binary_natural h611 hnatural hz horder hTH hstrict
  obtain ⟨heU, hUT⟩ := A.strict_binary_closure h611 hz hTH
  have hdN : d ∉ D.G₁ := by
    intro hh
    apply hdH
    have hc := normalizer_le_centralizer_of_card_two (zpowers z)
      ((Nat.card_zpowers z).trans horder) hh
    exact mem_centralizer_singleton_iff.mpr (hc z (mem_zpowers z)).symm
  obtain ⟨hn, _, hk⟩ := A.strict_binary_action h611 hnatural hz horder hTH hstrict
  have hk' := ChapterG.Section02.Setup.binary_source_star_kernel h b hUT d hdres hdN
  have hIL := ChapterG.Section02.Setup.binary_I_le_LT hUT hdres
  have hP : D.S d = D.I d ⊓ centralizer (D.V : Set G) := by
    have hq : pCore 2 (D.I d) = (centralizer (D.V : Set G)).subgroupOf (D.I d) := by
      rw [← hk', ChapterG.Section02.Setup.binaryStarRestriction_ker, ← hk,
        ← MonoidHom.comap_ker, normalizerMonoidHom_ker]
      rfl
    change (pCore 2 (D.I d)).map (D.I d).subtype = _
    rw [hq, subgroupOf_map_subtype, inf_comm]
  have hW : D.W d = sourceClosure (T : Subgroup G) L R z ⊓ centralizer (D.V : Set G) := by
    change D.U ⊓ D.S d = _
    rw [hP, ← inf_assoc, inf_eq_left.mpr (show D.U ≤ D.I d from le_sup_left), heU]
  have hdZ : d ∈ normalizer (D.V : Set G) := ((map_subtype_le _) hdres).2
  have hc : (centralizer (D.V : Set G)).map (MulAut.conj d⁻¹).toMonoidHom = centralizer (D.V : Set G) :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (centralizer (D.V : Set G) : Set G)).inv_mem
      (normalizer_le_normalizer_centralizer D.V hdZ))
  refine ⟨?_, hP, hW, ?_⟩
  · change D.U ⊓ D.U.map (MulAut.conj d⁻¹).toMonoidHom = _
    rw [heU]
    rfl
  · change (D.W d).map (MulAut.conj d⁻¹).toMonoidHom = _
    rw [hW, map_inf _ _ _ (MulAut.conj d⁻¹).injective, hc]
    rfl

/-- The natural opposite-factor module in 6.2.17, constructed by G.2.3
from the original source data. The quotient is the literal O₂(⟨U,Uᵈ⟩)/E. -/
theorem LocalAnalysis.strict_binary_crossing_module
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    let D := strictBinarySetup (T : Subgroup G) L R z
    let W := sourceClosure (T : Subgroup G) L R z ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)
    let X := strictCrossingGroup (T : Subgroup G) L R z d
    D.U = sourceClosure (T : Subgroup G) L R z ∧
    D.S₂ d = strictCrossingIntersection (T : Subgroup G) L R z d ∧
    D.S d = D.I d ⊓ centralizer (ZS (T : Subgroup G) L R : Set G) ∧
    D.I d = strictCrossingResidual (T : Subgroup G) L R ⊔ sourceClosure (T : Subgroup G) L R z ∧
    D.S d = W ⊔ X ∧
    ∃ (e : (D.I d ⧸ pCore 2 (D.I d)) ≃* Equiv.Perm (Fin 3))
      (hN : ((D.S₂ d).subgroupOf (D.S d)).Normal),
      letI := hN
      ∃ hA : IsElementaryAbelian 2 (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d)),
        letI := hA
        ∃ (σ : Representation (ZMod 2) (Equiv.Perm (Fin 3))
          (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))
          (c : Representation.BinaryConjugationSection (D.I d) (D.S d) (D.S₂ d)
            (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I d)))))),
          D.V ≤ D.S₂ d ∧ D.S₂ d ≤ D.S d ∧
          ((D.S₂ d).subgroupOf (D.I d)).Normal ∧
          ⁅D.S₂ d, D.I d⁆ ≤ D.V ∧ IsElementaryAbelian 2 (D.S₂ d) ∧
          (∀ s : D.S d, (c.coordinates s).toAdd =
            Additive.ofMul (QuotientGroup.mk' ((D.S₂ d).subgroupOf (D.S d)) s)) ∧
          Finite (InvertedCubicTensor.multiplicitySpace σ) ∧
          IsCompl (c.imageSpace W) (c.imageSpace X) ∧
          (∃ j : InvertedCubicTensor.multiplicitySpace σ ⊗[ZMod 2] BinaryPermutation.core (Fin 3) ≃ₗ[ZMod 2]
                Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d)),
              ∀ a v, j ((Representation.tprod (Representation.trivial (ZMod 2) (Equiv.Perm (Fin 3))
                  (InvertedCubicTensor.multiplicitySpace σ)) (BinaryPermutation.coreRepresentation (Fin 3))) a v) =
                σ a (j v)) ∧
          (∀ u : D.I d, (u : G) ∈ sourceClosure (T : Subgroup G) L R z → (u : G) ∉ W →
            LinearMap.ker (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - (1 : Module.End (ZMod 2) (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))) = c.imageSpace W ∧
            LinearMap.range (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - (1 : Module.End (ZMod 2) (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))) = c.imageSpace W ∧
            (c.imageSpace X).map (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - (1 : Module.End (ZMod 2) (Additive (D.S d ⧸ (D.S₂ d).subgroupOf (D.S d))))) = c.imageSpace W) := by
  let D := strictBinarySetup (T : Subgroup G) L R z
  have h := A.strict_binary_hypothesis h611 hnatural hz horder hTH
  let b := A.strict_binary_natural h611 hnatural hz horder hTH hstrict
  obtain ⟨heU, hUT⟩ := A.strict_binary_closure h611 hz hTH
  have hdN : d ∉ D.G₁ := by
    intro hh
    apply hdH
    have hc := normalizer_le_centralizer_of_card_two (zpowers z)
      ((Nat.card_zpowers z).trans horder) hh
    exact mem_centralizer_singleton_iff.mpr (hc z (mem_zpowers z)).symm
  have hf : (frattini D.U).map D.U.subtype ≤ D.V₁ := by
    rw [heU]
    exact (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1.le
  obtain ⟨hI, _, hnorm, hindex, _⟩ := ChapterG.Section02.Setup.binary_source_inputs h b hUT d hdres hdN
  let e := ChapterG.Section02.Setup.binarySourceCoreEquiv h b hUT d hdres hdN
  obtain ⟨hN, hA, σ, c, hS, _, hVE, hEP, _, _, hEN, hEC, hEE, hcoord,
    hfinite, hcompl, htensor, _, hmarks, _⟩ :=
    D.binary_source_clauses_three_to_seven h b hUT hf d hdres hdN hI e hnorm hindex
  obtain ⟨hE, hP, hW, hX⟩ := A.strict_binary_crossing_identifications h611 hnatural hz horder hTH hstrict hdres hdH
  let c' : Representation.BinaryConjugationSection (D.I d) (D.S d) (D.S₂ d)
      (σ.comp (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 (D.I d))))) := by
    exact { c with
      equivariant := by
        intro a v
        simpa only [ChapterG.Section02.Setup.binaryCoreProjection_eq] using c.equivariant a v }
  have hI' : D.I d = strictCrossingResidual (T : Subgroup G) L R ⊔ sourceClosure (T : Subgroup G) L R z := by
    rw [hI, heU]
    rfl
  refine ⟨heU, hE, hP, hI', ?_, e, hN, hA, σ, c', hVE, hEP, hEN, hEC, hEE,
    hcoord, hfinite, ?_, htensor, ?_⟩
  · exact hS.trans (congrArg₂ (· ⊔ ·) hW hX)
  · change IsCompl (c.imageSpace _) (c.imageSpace _)
    rw [← hW, ← hX]
    exact hcompl
  · intro u hu huw
    have hm := hmarks u (heU.ge hu) (fun hh => huw (hW.le hh))
    change LinearMap.ker (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - 1) = c.imageSpace _ ∧
      LinearMap.range (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - 1) = c.imageSpace _ ∧
      (c.imageSpace _).map (σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) u)) - 1) = c.imageSpace _
    rw [← hW, ← hX]
    simpa only [ChapterG.Section02.Setup.binaryCoreProjection_eq, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom] using hm

/-- The opposite subgroup meets the original two-core in exactly E. -/
theorem LocalAnalysis.strict_crossing_core_intersection
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G)) :
    strictCrossingGroup (T : Subgroup G) L R z d ⊓ (centralizer ({z} : Set G)).pCoreIn 2 =
      strictCrossingIntersection (T : Subgroup G) L R z d := by
  let D := strictBinarySetup (T : Subgroup G) L R z
  have h := A.strict_binary_hypothesis h611 hnatural hz horder hTH
  let b := A.strict_binary_natural h611 hnatural hz horder hTH hstrict
  obtain ⟨heU, hUT⟩ := A.strict_binary_closure h611 hz hTH
  have hdN : d ∉ D.G₁ := by
    intro hh
    apply hdH
    have hc := normalizer_le_centralizer_of_card_two (zpowers z)
      ((Nat.card_zpowers z).trans horder) hh
    exact mem_centralizer_singleton_iff.mpr (hc z (mem_zpowers z)).symm
  have hf : (frattini D.U).map D.U.subtype ≤ D.V₁ := by
    rw [heU]
    exact (A.strict_closure_frattini_eq_line h611 hnatural hz horder hstrict).1.le
  have hUQ : D.U ≤ D.QH := heU.le.trans A.closure_le_core
  have hcomm : ⁅D.U, D.QH⁆ ≤ D.V₁ := by
    rw [heU]
    exact A.closure_core_commutator
  have he := (ChapterG.Section02.Setup.binary_source_core_intersection_and_index
    h b hUT hf hUQ hcomm d hdres hdN).1
  obtain ⟨hE, _, _, hX⟩ := A.strict_binary_crossing_identifications h611 hnatural hz horder hTH hstrict hdres hdH
  exact (congrArg (fun Y : Subgroup G => Y ⊓ D.QH) hX).symm.trans (he.trans hE)

/-- Before passing to U/Z(U), a fixed vector outside C_U(Z_S) forces
an opposite actor into E. This uses the actual natural crossing module. -/
theorem LocalAnalysis.strict_crossing_tilde_fixed_bound
    (A : LocalAnalysis (T : Subgroup G) L M R z)
    (h611 : Hypothesis611 κ T L M R n)
    (hnatural : Conclusion6127 (T : Subgroup G) L M R n)
    (hz : z ∈ ZS (T : Subgroup G) L R) (horder : orderOf z = 2)
    (hTH : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hstrict : ZS (T : Subgroup G) L R < sourceClosure (T : Subgroup G) L R z ⊓ layer L R)
    {d : G} (hdres : d ∈ strictCrossingResidual (T : Subgroup G) L R)
    (hdH : d ∉ centralizer ({z} : Set G))
    {x u : G} (hx : x ∈ strictCrossingGroup (T : Subgroup G) L R z d)
    (hu : u ∈ sourceClosure (T : Subgroup G) L R z)
    (huw : u ∉ centralizer (ZS (T : Subgroup G) L R : Set G))
    (hfix : ⁅x,u⁆ ∈ zpowers z) :
    x ∈ strictCrossingIntersection (T : Subgroup G) L R z d := by
  obtain ⟨heU, hE, _, _, hP, e, hN, hA, σ, c, hVE, _, _, _, _, _, _, hcompl, _, hmarks⟩ :=
    A.strict_binary_crossing_module h611 hnatural hz horder hTH hstrict hdres hdH
  let D := strictBinarySetup (T : Subgroup G) L R z
  let := hN
  let := hA
  let W := sourceClosure (T : Subgroup G) L R z ⊓ centralizer (ZS (T : Subgroup G) L R : Set G)
  let X := strictCrossingGroup (T : Subgroup G) L R z d
  have hxP : x ∈ D.S d := hP.ge (mem_sup_right hx)
  let xp : D.S d := ⟨x, hxP⟩
  let ui : D.I d := ⟨u, mem_sup_left (heU.ge hu)⟩
  have hfx : σ (e (QuotientGroup.mk' (pCore 2 (D.I d)) ui)) (c.coordinates xp).toAdd =
      (c.coordinates xp).toAdd := by
    apply (c.fixed_coordinate_iff_commutator_mem ui xp).mpr
    exact hVE (zpowers_le.mpr hz hfix)
  have hxX : (c.coordinates xp).toAdd ∈ c.imageSpace X :=
    (c.mem_imageSpace_iff X _).mpr ⟨xp, hx, rfl⟩
  have hxW : (c.coordinates xp).toAdd ∈ c.imageSpace W := by
    rw [← (hmarks ui hu (fun h => huw h.2)).1]
    exact sub_eq_zero.mpr hfx
  have hzero : c.coordinates xp = 1 := hcompl.disjoint.le_bot ⟨hxW, hxX⟩
  exact hE.le ((c.coordinates_eq_one_iff xp).mp hzero)

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
