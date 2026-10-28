module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.SectionThree.CriticalModules.LocalStructure

/-!
# The actual elementary layers in the binary natural-structure argument

The fixed part of X is already in Z: it centralizes the whole vertex group,
hence lies in the omega-center of every adjacent edge kernel. Consequently
a decomposition of X into U and its fixed part also proves X = Z.

These are preparations for, and the elementary last step of, the binary
parts of MS93 (3.2), (3.8), and (4.1). The module classification and exclusion
of the doubled and nonsplit alternatives are not assumed as source facts.

Source: Meierfrankenfeld--Stellmacher (1993), pp.856--857, 863, 877--882.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- Since Q centralizes X, residual-fixed elements of X are fixed by G. -/
theorem LocalSource.X_fixed_eq_stabilizer_fixed (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) =
      X R a ⊓ centralizer (stabilizer R a : Set (FreeAmalgam R)) := by
  apply le_antisymm
  · intro x hx
    refine ⟨hx.1, ?_⟩
    have hgen : Ltilde R a ⊔ Q R a ≤ centralizer ({x} : Set (FreeAmalgam R)) := by
      apply sup_le
      · intro g hg
        exact mem_centralizer_singleton_iff.mpr (hx.2 g hg)
      · intro g hg
        exact mem_centralizer_singleton_iff.mpr
          ((mem_omegaCenter_iff.mp hx.1).2.2 g hg)
    rw [source.local_generation a ha] at hgen
    intro g hg
    exact mem_centralizer_singleton_iff.mp (hgen hg)
  · exact inf_le_inf_left _ (centralizer_le (Ltilde_le_stabilizer a))

/-- A vector in X fixed by the residual lies in the source-generated layer Z.
This uses the literal omega-center at an adjacent holomorph vertex. -/
theorem LocalSource.X_fixed_le_Z (source : LocalSource L R)
    (a : Vertex R) (ha : color R a = false) :
    X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)) ≤ Z R a := by
  intro x hx
  have hxQ : x ∈ Q R a := omegaCenter_le _ hx.1
  have hcentral : x ∈ centralizer (stabilizer R a : Set (FreeAmalgam R)) :=
    ((source.X_fixed_eq_stabilizer_fixed a ha).le hx).2
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hat : Adjacent R (mVertex R g) (hVertex R g) := by
    simpa only [act_mVertex, act_hVertex, one_mul] using
      (adjacent_act_iff R g _ _).mpr (base_adjacent R)
  have hxt : x ∈ edgeOmega R (hVertex R g) := by
    apply mem_omegaCenter_iff.mpr
    refine ⟨Q_le_adjacent_h R rfl hat hxQ, (mem_omegaCenter_iff.mp hx.1).2.1, ?_⟩
    intro y hy
    exact hcentral y (hy.2 _ (adjacent_symm R hat))
  rw [Z, if_pos (show color R (mVertex R g) = false from rfl)]
  have hle : edgeOmega R (hVertex R g) ≤
      ⨆ t, ⨆ (_ : Adjacent R (mVertex R g) t), edgeOmega R t :=
    le_iSup_of_le (hVertex R g) (le_iSup_of_le hat le_rfl)
  exact hle hxt

/-- Once the source 3.8 splitting of X is proved, source 4.1(i) follows. -/
theorem LocalSource.X_eq_Z_of_decomposition (source : LocalSource L R)
    (geometry : Geometry R) (hb : 0 < geometry.b R)
    (a : Vertex R) (ha : color R a = false)
    (hsplit : X R a = U R a ⊔
      (X R a ⊓ centralizer (Ltilde R a : Set (FreeAmalgam R)))) : X R a = Z R a := by
  apply le_antisymm
  · rw [hsplit]
    exact sup_le (U_le_Z a) (source.X_fixed_le_Z a ha)
  · apply geometry.omega_bound a ha
    rw [geometry.distance_constant a ha]
    exact hb

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
