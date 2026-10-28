module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Source
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.LineCore

/-!
# The three incident cores in the binary parabolic

Two distinct opposite cores generate the full first parabolic and meet trivially
in SL₃(2). Three-factor matrix words prove generation; coset representatives of
the Borel enumerate the three neighbors. The diagram automorphism transports
the calculation to the other color before the given flag conjugation is applied.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.906.
-/

@[expose] public section
open Subgroup Matrix Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.FixedSpaceModel
abbrev G := Matrix.PSL3Two.SL

def core (t : G) (i : Bool) (g : G) : Subgroup G :=
  ((modelParabolic t i).pCoreIn 2).map (MulAut.conj g).toMonoidHom

private abbrev C {X : Type*} [Group X] (A : Subgroup X) (g : X) :=
  A.map (MulAut.conj g).toMonoidHom
private def c : G := ⟨!![1,0,0;0,0,1;0,1,1], by decide⟩
private def rep (j : Fin 3) : G := c ^ j.val
private def u (v : ZMod 2 × ZMod 2) : G := BinaryLinearThree.shear (Multiplicative.ofAdd v)
private def gen (j : Fin 3) (v : ZMod 2 × ZMod 2) : G := (MulAut.conj (rep j)) (u v)

private theorem rep_mem (j : Fin 3) : rep j ∈ pointParabolicSL := by
  exact pow_mem (by decide : c ∈ pointParabolicSL) _

private theorem core_mem (j : Fin 3) (v : ZMod 2 × ZMod 2) :
    gen j v ∈ C (lineParabolicSL.pCoreIn 2) (rep j) := by
  rw [lineParabolicSL_pCoreIn_two_eq_R]
  exact mem_map_of_mem _ ⟨Multiplicative.ofAdd v, rfl⟩

private theorem core_le (j : Fin 3) :
    C (lineParabolicSL.pCoreIn 2) (rep j) ≤ pointParabolicSL := by
  have h : ∀ j : Fin 3, ∀ v : ZMod 2 × ZMod 2, gen j v ∈ pointParabolicSL := by decide +kernel
  rw [lineParabolicSL_pCoreIn_two_eq_R]
  rintro x ⟨y, ⟨v, rfl⟩, rfl⟩
  exact h j v.toAdd

private theorem words (x : G) (hx : x ∈ pointParabolicSL) :
    ∃ a b d : ZMod 2 × ZMod 2, x = gen 0 a * gen 1 b * gen 0 d := by
  revert x hx
  decide +kernel

private theorem base_sup :
    C (lineParabolicSL.pCoreIn 2) (rep 0) ⊔
      C (lineParabolicSL.pCoreIn 2) (rep 1) = pointParabolicSL := by
  apply le_antisymm (sup_le (core_le 0) (core_le 1))
  intro x hx
  obtain ⟨a,b,d,rfl⟩ := words x hx
  exact mul_mem (mul_mem (mem_sup_left (core_mem 0 a))
    (mem_sup_right (core_mem 1 b))) (mem_sup_left (core_mem 0 d))

private theorem base_inf :
    C (lineParabolicSL.pCoreIn 2) (rep 0) ⊓
      C (lineParabolicSL.pCoreIn 2) (rep 1) = ⊥ := by
  apply eq_bot_iff.mpr
  rw [lineParabolicSL_pCoreIn_two_eq_R]
  rintro x ⟨⟨a,⟨v,rfl⟩,rfl⟩, b,⟨w,rfl⟩,he⟩
  have test : ∀ v w : ZMod 2 × ZMod 2,
      gen 1 w = gen 0 v → gen 0 v = 1 := by decide +kernel
  exact test v.toAdd w.toAdd he

private theorem conjugate_mul {X : Type*} [Group X] (A : Subgroup X) (g h : X) :
    C (C A h) g = C A (g*h) := by
  unfold C
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, _root_.mul_inv_rev]
  group

private theorem rotate (A : Subgroup G) (j : Fin 3) :
    C (C A (rep j)) c = C A (rep (j + 1)) := by
  rw [conjugate_mul]
  congr 1
  revert j
  decide +kernel

private theorem rotate_parabolic : C pointParabolicSL c = pointParabolicSL :=
  mem_normalizer_iff_map_conj_eq.mp (pointParabolicSL.le_normalizer (by decide))

private theorem pair_sup (j k : Fin 3) (hjk : j ≠ k) :
    C (lineParabolicSL.pCoreIn 2) (rep j) ⊔
      C (lineParabolicSL.pCoreIn 2) (rep k) = pointParabolicSL := by
  have h01 := base_sup
  have h12 := congrArg (fun A : Subgroup G => C A c) h01
  simp only [Subgroup.map_sup, rotate, rotate_parabolic] at h12
  have h20 := congrArg (fun A : Subgroup G => C A c) h12
  simp only [Subgroup.map_sup, rotate, rotate_parabolic] at h20
  fin_cases j <;> fin_cases k
  · exact False.elim (hjk rfl)
  · exact h01
  · exact (sup_comm _ _).trans h20
  · exact (sup_comm _ _).trans h01
  · exact False.elim (hjk rfl)
  · exact h12
  · exact h20
  · exact (sup_comm _ _).trans h12
  · exact False.elim (hjk rfl)

private theorem pair_inf (j k : Fin 3) (hjk : j ≠ k) :
    C (lineParabolicSL.pCoreIn 2) (rep j) ⊓
      C (lineParabolicSL.pCoreIn 2) (rep k) = ⊥ := by
  have h01 := base_inf
  have h12 := congrArg (fun A : Subgroup G => C A c) h01
  simp only [map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective, rotate, Subgroup.map_bot] at h12
  have h20 := congrArg (fun A : Subgroup G => C A c) h12
  simp only [map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective, rotate, Subgroup.map_bot] at h20
  fin_cases j <;> fin_cases k
  · exact False.elim (hjk rfl)
  · exact h01
  · exact (inf_comm _ _).trans h20
  · exact (inf_comm _ _).trans h01
  · exact False.elim (hjk rfl)
  · exact h12
  · exact h20
  · exact (inf_comm _ _).trans h12
  · exact False.elim (hjk rfl)

private theorem cover (x : G) (hx : x ∈ pointParabolicSL) :
    ∃ j : Fin 3, (rep j)⁻¹ * x ∈ lineParabolicSL := by
  revert x hx
  decide +kernel

private theorem mapping (t : G) (i : Bool) : ∃ e : MulAut G,
    pointParabolicSL.map e.toMonoidHom = modelParabolic t i ∧
    lineParabolicSL.map e.toMonoidHom = modelParabolic t (!i) := by
  cases i
  · exact ⟨MulAut.conj t, rfl, rfl⟩
  · refine ⟨MulAut.conj t * diagram, ?_, ?_⟩
    · change pointParabolicSL.map ((MulAut.conj t).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← Subgroup.map_map, pointParabolic_map_diagram]
      rfl
    · have hl : lineParabolicSL.map diagram.toMonoidHom = pointParabolicSL := by
        ext x
        constructor
        · rintro ⟨x,hx,rfl⟩
          have h := (diagram_point_line (diagram x)).mp
            (by rwa [diagram_involutive])
          exact h
        · intro hx
          exact ⟨diagram x, (diagram_point_line x).mpr hx, diagram_involutive x⟩
      change lineParabolicSL.map ((MulAut.conj t).toMonoidHom.comp diagram.toMonoidHom) = _
      rw [← Subgroup.map_map, hl]
      rfl

private theorem map_conj {X : Type*} [Group X] (A : Subgroup X) (g : X) (e : MulAut X) :
    (C A g).map e.toMonoidHom = C (A.map e.toMonoidHom) (e g) := by
  unfold C
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

/-- The three actual incident cores, with pairwise full generation, trivial
intersection, and coverage of every incident parabolic coset. -/
theorem pencil (t : G) (i : Bool) :
    ∃ d : Fin 3 → G,
      (∀ j, d j ∈ modelParabolic t i) ∧
      (∀ j k, j ≠ k → core t (!i) (d j) ⊔ core t (!i) (d k) = modelParabolic t i) ∧
      (∀ j k, j ≠ k → core t (!i) (d j) ⊓ core t (!i) (d k) = ⊥) ∧
      (∀ a ∈ modelParabolic t i, ∃ j, (d j)⁻¹ * a ∈ modelParabolic t (!i)) := by
  obtain ⟨e,hP,hQ⟩ := mapping t i
  have hc (j : Fin 3) : core t (!i) (e (rep j)) =
      (C (lineParabolicSL.pCoreIn 2) (rep j)).map e.toMonoidHom := by
    rw [core, ← hQ, ← map_pCoreIn_of_injective 2 _ _ e.injective]
    exact (map_conj _ _ _).symm
  refine ⟨fun j => e (rep j), (fun j => hP ▸ mem_map_of_mem _ (rep_mem j)), ?_, ?_, ?_⟩
  · intro j k hjk
    rw [hc, hc, ← Subgroup.map_sup, pair_sup j k hjk, hP]
  · intro j k hjk
    rw [hc, hc, ← map_inf _ _ _ e.injective, pair_inf j k hjk, Subgroup.map_bot]
  · intro a ha
    obtain ⟨x,rfl⟩ := e.surjective a
    have hx : x ∈ pointParabolicSL := (mem_map_iff_mem e.injective).mp (hP.symm ▸ ha)
    obtain ⟨j,hj⟩ := cover x hx
    refine ⟨j, ?_⟩
    have hh := mem_map_of_mem e.toMonoidHom hj
    rw [hQ] at hh
    simpa only [map_mul, map_inv, MulEquiv.coe_toMonoidHom] using hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.Incident.FixedSpaceModel
