module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.LocalFacts

/-!
# Conjugation covariance in the MS93 right-coset graph

Right multiplication sends a local subgroup to its conjugate by the inverse
multiplier. We prove that equation for first-neighborhood kernels, omega
centers, Z-layers and every radius subgroup. Mapping shortest walks in both
directions preserves graph distance. Consequently the least critical distance
is unchanged along an orbit. Z is normal in its actual vertex stabilizer.

These are transport statements on the original infinite free amalgam, with
no tree or classification assumption. Source: MS93 (1993), pp.854--855.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] (R : Subgroup M)

def actEquiv (g : FreeAmalgam R) : Vertex R ≃ Vertex R where
  toFun := act R g
  invFun := act R g⁻¹
  left_inv a := by rw [← act_mul]; simp
  right_inv a := by rw [← act_mul]; simp

def actGraphHom (g : FreeAmalgam R) : cosetGraph R →g cosetGraph R where
  toFun := act R g
  map_rel' := by
    intro a b hab
    exact (cosetGraph_adj R _ _).mpr
      ((adjacent_act_iff R g a b).mpr ((cosetGraph_adj R _ _).mp hab))

theorem dist_act (g : FreeAmalgam R) (a b : Vertex R) :
    (cosetGraph R).dist (act R g a) (act R g b) = (cosetGraph R).dist a b := by
  have hle (g : FreeAmalgam R) (a b : Vertex R) :
      (cosetGraph R).dist (act R g a) (act R g b) ≤ (cosetGraph R).dist a b := by
    obtain ⟨p, hp⟩ := (cosetGraph_connected R).exists_walk_length_eq_dist a b
    have ht := SimpleGraph.dist_le (p.map (actGraphHom R g))
    change (cosetGraph R).dist (act R g a) (act R g b) ≤ _ at ht
    simpa only [SimpleGraph.Walk.length_map, hp] using ht
  apply le_antisymm (hle g a b)
  have ht := hle g⁻¹ (act R g a) (act R g b)
  simpa only [← act_mul, mul_inv_cancel, act_one] using ht

private theorem mem_map_conj (A : Subgroup (FreeAmalgam R)) (g x : FreeAmalgam R) :
    x ∈ A.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * x * g⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro hx
    exact ⟨g * x * g⁻¹, hx, by simp [mul_assoc]⟩

private theorem mem_stabilizer_act (g x : FreeAmalgam R) (a : Vertex R) :
    x ∈ stabilizer R (act R g a) ↔ g * x * g⁻¹ ∈ stabilizer R a := by
  rw [stabilizer_act, mem_map_conj]

theorem Q_act (g : FreeAmalgam R) (a : Vertex R) :
    Q R (act R g a) = (Q R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  ext x
  rw [mem_map_conj]
  constructor
  · intro hx
    refine ⟨(mem_stabilizer_act R g x a).mp hx.1, ?_⟩
    intro b hab
    exact (mem_stabilizer_act R g x b).mp
      (hx.2 (act R g b) ((adjacent_act_iff R g a b).mpr hab))
  · intro hx
    refine ⟨(mem_stabilizer_act R g x a).mpr hx.1, ?_⟩
    intro b hab
    have hab' : Adjacent R a (act R g⁻¹ b) := by
      have hh := (adjacent_act_iff R g⁻¹ (act R g a) b).mpr hab
      simpa only [← act_mul, mul_inv_cancel, act_one] using hh
    have hh := (mem_stabilizer_act R g x (act R g⁻¹ b)).mpr (hx.2 _ hab')
    simpa only [← act_mul, inv_mul_cancel, act_one] using hh

theorem edgeOmega_act (g : FreeAmalgam R) (a : Vertex R) :
    edgeOmega R (act R g a) = (edgeOmega R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [edgeOmega, Q_act, omegaCenter_map _ _ (MulAut.conj g⁻¹).injective]
  rfl

theorem Z_act (g : FreeAmalgam R) (a : Vertex R) :
    Z R (act R g a) = (Z R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  classical
  rw [Z, action_preserves_color, Z]
  by_cases ha : color R a = false
  · simp only [ha, if_true, Subgroup.map_iSup]
    apply le_antisymm
    · apply iSup_le
      intro b
      apply iSup_le
      intro hb
      have hb' : Adjacent R a (act R g⁻¹ b) := by
        have hh := (adjacent_act_iff R g⁻¹ (act R g a) b).mpr hb
        simpa only [← act_mul, mul_inv_cancel, act_one] using hh
      refine le_iSup_of_le (act R g⁻¹ b) (le_iSup_of_le hb' ?_)
      rw [← edgeOmega_act]
      simp only [← act_mul, inv_mul_cancel, act_one, le_refl]
    · apply iSup_le
      intro b
      apply iSup_le
      intro hb
      refine le_iSup_of_le (act R g b)
        (le_iSup_of_le ((adjacent_act_iff R g a b).mpr hb) ?_)
      rw [edgeOmega_act]
  · simp only [ha]
    exact edgeOmega_act R g a

theorem VBall_act (g : FreeAmalgam R) (a : Vertex R) (i : ℕ) :
    VBall R (act R g a) i = (VBall R a i).map (MulAut.conj g⁻¹).toMonoidHom := by
  simp only [VBall, Subgroup.map_iSup]
  apply le_antisymm
  · apply iSup_le
    intro b
    apply iSup_le
    intro hb
    have hb' : (cosetGraph R).dist (act R g⁻¹ b) a ≤ i := by
      have hh := dist_act R g⁻¹ b (act R g a)
      simpa only [← act_mul, mul_inv_cancel, act_one] using hh.le.trans hb
    refine le_iSup_of_le (act R g⁻¹ b) (le_iSup_of_le hb' ?_)
    rw [← Z_act]
    simp only [← act_mul, inv_mul_cancel, act_one, le_refl]
  · apply iSup_le
    intro b
    apply iSup_le
    intro hb
    refine le_iSup_of_le (act R g b) (le_iSup_of_le (by rwa [dist_act]) ?_)
    rw [Z_act]

theorem Z_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (Z R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (Z R a).map (MulAut.conj g).toMonoidHom = Z R a
  have hh := Z_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using hh.symm

theorem Z_normal (a : Vertex R) : ((Z R a).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (Z_normalized R a)

theorem criticalRadius_act_iff (g : FreeAmalgam R) (a : Vertex R) (n : ℕ) :
    CriticalRadius R (act R g a) n ↔ CriticalRadius R a n := by
  have one_way (g : FreeAmalgam R) (a : Vertex R) :
      CriticalRadius R a n → CriticalRadius R (act R g a) n := by
    rintro ⟨b, hd, hn⟩
    refine ⟨act R g b, by rwa [dist_act], ?_⟩
    rw [Z_act, Q_act]
    intro h
    apply hn
    exact (map_le_map_iff_of_injective (MulAut.conj g⁻¹).injective).mp h
  constructor
  · intro h
    have hh := one_way g⁻¹ (act R g a) h
    simpa only [← act_mul, mul_inv_cancel, act_one] using hh
  · exact one_way g a

theorem criticalDistance_act (g : FreeAmalgam R) (a : Vertex R)
    (he : ∃ n, CriticalRadius R a n)
    (he' : ∃ n, CriticalRadius R (act R g a) n) :
    criticalDistance R (act R g a) he' = criticalDistance R a he := by
  classical
  apply le_antisymm
  · exact Nat.find_min' he' ((criticalRadius_act_iff R g a _).mpr (Nat.find_spec he))
  · exact Nat.find_min' he ((criticalRadius_act_iff R g a _).mp (Nat.find_spec he'))

theorem Ltilde_act (g : FreeAmalgam R) (a : Vertex R) :
    Ltilde R (act R g a) = (Ltilde R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  let e := MulAut.conj g⁻¹
  rw [Ltilde, stabilizer_act, Ltilde]
  change (pResidual 2 ((stabilizer R a).map (e : FreeAmalgam R →* FreeAmalgam R))).map
      ((stabilizer R a).map (e : FreeAmalgam R →* FreeAmalgam R)).subtype =
    ((pResidual 2 (stabilizer R a)).map (stabilizer R a).subtype).map
      (e : FreeAmalgam R →* FreeAmalgam R)
  rw [← map_pResidual 2 (e.subgroupMap (stabilizer R a)), map_map, map_map]
  rfl

theorem core_act (g : FreeAmalgam R) (a : Vertex R) :
    core R (act R g a) = (core R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [core, Q_act, Ltilde_act, ← map_commutator]
  rfl

theorem U_act (g : FreeAmalgam R) (a : Vertex R) :
    U R (act R g a) = (U R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [U, Z_act, Ltilde_act, ← map_commutator]
  rfl

theorem V_act (g : FreeAmalgam R) (a : Vertex R) :
    V R (act R g a) = (V R a).map (MulAut.conj g⁻¹).toMonoidHom := VBall_act R g a 2

theorem Vcirc_act (g : FreeAmalgam R) (a : Vertex R) :
    Vcirc R (act R g a) = (Vcirc R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [Vcirc, V_act, Ltilde_act, ← map_commutator]
  rfl

theorem H_act (g : FreeAmalgam R) (a : Vertex R) :
    H R (act R g a) = (H R a).map (MulAut.conj g⁻¹).toMonoidHom := by
  rw [H, Vcirc_act, Q_act, ← map_commutator]
  rfl

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
