module
public import Theory.SpecificGroups.SL2.SylowCharacteristicImage
public import Glauberman.BaumannClosureTransport

/-!
# Opposite generators for the all-abelian Baumann closure

In a finite group with its actual SL₂ quotient at characteristic two, the
Baumann subgroup of a Sylow has full Sylow image whenever it escapes the
whole two-core. Normalizer invariance and the Borel torus prove this without
any restriction on the original field degree. Thus the Sylow is B O₂(G),
and an element of the original two-residual gives two Baumann conjugates
that generate modulo O₂(G).

When B normally generates G, it also supplements O²(G). The intersection
of the two conjugate Thompson central omega subgroups is precisely their
central part. Indeed the core normalizes both omega subgroups, while the
two Baumann conjugates centralize their intersection. Generation makes
that intersection normal; normal generation by B then makes it central.

Source: the Baumann preparation in MS93 (5.1), printed p.913. The literal
replacement application is CriticalReduction.RootProductOpposites. The
remaining core-centralization argument is necessary before identifying B
with the Sylow, and is not assumed in these results.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Glauberman
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] [Finite F] [CharP F 2] in
private theorem map_conjugate (q : G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (A : Subgroup G) (x : G) :
    (A.map (MulAut.conj x).toMonoidHom).map q =
      (A.map q).map (MulAut.conj (q x)).toMonoidHom := by
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro y
  change q (x * y * x⁻¹) = q x * q y * (q x)⁻¹
  simp only [map_mul,map_inv]

/-- Baumann covers the full original Sylow image, and two residual conjugates generate modulo the core. -/
theorem baumann_rank_one_generation
    (S : Sylow 2 G) (q : G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    (hB : ¬ baumannSubgroup (S : Subgroup G) ≤ pCore 2 G) :
    (baumannSubgroup (S : Subgroup G)).map q = (S : Subgroup G).map q ∧
    baumannSubgroup (S : Subgroup G) ⊔ pCore 2 G = (S : Subgroup G) ∧
    ∃ x : G, x ∈ pResidual 2 G ∧
      (baumannSubgroup (S : Subgroup G) ⊔
        (baumannSubgroup (S : Subgroup G)).map (MulAut.conj x).toMonoidHom) ⊔
          pCore 2 G = ⊤ := by
  let B := baumannSubgroup (S : Subgroup G)
  have hm := Matrix.SpecialLinearGroup.normalizer_invariant_image_eq_sylow S q hq B
    inf_le_left (by rwa [hk]) (normalizer_le_normalizer_baumannSubgroup _)
  have hsup : B ⊔ pCore 2 G = (S : Subgroup G) := by
    have hh := congrArg (Subgroup.comap q) hm
    rwa [comap_map_eq,comap_map_eq,hk,
      sup_eq_left.mpr (pCore_isPGroup.le_sylow_of_normal S)] at hh
  obtain ⟨x,hx,hgen⟩ :=
    Matrix.SpecialLinearGroup.exists_residual_conjugate_sylow_image_sup_eq_top S q hq
  rw [map_conjugate,←hm,←map_conjugate] at hgen
  have hh := congrArg (Subgroup.comap q) hgen
  rw [←Subgroup.map_sup,comap_map_eq,hk,comap_top] at hh
  exact ⟨hm,hsup,x,hx,hh⟩

omit [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- The two opposite all-abelian central omegas meet exactly in their full central part. -/
theorem baumann_opposite_omega_intersection
    (S : Sylow 2 G)
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤)
    (x : G)
    (hopp : (baumannSubgroup (S : Subgroup G) ⊔
        (baumannSubgroup (S : Subgroup G)).map (MulAut.conj x).toMonoidHom) ⊔
          pCore 2 G = ⊤) :
    omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊓
      (omegaCenterIn (thompsonSubgroup (S : Subgroup G))).map (MulAut.conj x).toMonoidHom =
    omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊓ center G := by
  let B := baumannSubgroup (S : Subgroup G)
  let Z := omegaCenterIn (thompsonSubgroup (S : Subgroup G))
  let e := (MulAut.conj x).toMonoidHom
  let Y := Z ⊓ Z.map e
  have hSZ : (S : Subgroup G) ≤ normalizer (Z : Set G) :=
    (S : Subgroup G).le_normalizer.trans
      ((normalizer_le_normalizer_of_thompsonSubgroup _).trans
        (normalizer_le_normalizer_omegaCenterIn _))
  have hQZ : pCore 2 G ≤ normalizer (Z : Set G) :=
    (pCore_isPGroup.le_sylow_of_normal S).trans hSZ
  have hQZx : pCore 2 G ≤ normalizer (Z.map e : Set G) := by
    rw [←map_normalizer_eq_of_bijective _ (MulAut.conj x).bijective]
    have hh := map_mono (f := e) hQZ
    have he : (pCore 2 G).map e = pCore 2 G := Normal.map_conj_eq _ x
    rwa [he] at hh
  have hQY : pCore 2 G ≤ normalizer (Y : Set G) :=
    (le_inf hQZ hQZx).trans inf_normalizer_le_normalizer_inf
  have hBY : B ≤ centralizer (Y : Set G) :=
    (show B ≤ centralizer (Z : Set G) from inf_le_right).trans (centralizer_le inf_le_left)
  have hBxY : B.map e ≤ centralizer (Y : Set G) := by
    have hz : ⁅Z.map e,B.map e⁆ = ⊥ := by
      rw [←map_commutator,commutator_comm,
        commutator_eq_bot_iff_le_centralizer.mpr (show B ≤ centralizer (Z : Set G) from inf_le_right),
        Subgroup.map_bot]
    exact le_centralizer_iff.mp
      (inf_le_right.trans (commutator_eq_bot_iff_le_centralizer.mp hz))
  let : Y.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hopp]
    exact sup_le (sup_le (hBY.trans (Subgroup.centralizer_le_normalizer _))
      (hBxY.trans (Subgroup.centralizer_le_normalizer _))) hQY
  have hCY : (⊤ : Subgroup G) ≤ centralizer (Y : Set G) := by
    rw [←hgen]
    exact normalClosure_le_normal hBY
  have hYcenter : Y ≤ center G := by
    intro y hy
    exact mem_center_iff.mpr (fun g => (hCY (mem_top g) y hy).symm)
  apply le_antisymm (le_inf inf_le_left hYcenter)
  intro z hz
  refine ⟨hz.1,⟨z,hz.1,?_⟩⟩
  change x * z * x⁻¹ = z
  rw [(mem_center_iff.mp hz.2 x),mul_inv_cancel_right]

omit [Field F] [Finite F] [CharP F 2] in
/-- A normally generating Baumann subgroup supplements the whole two-residual. -/
theorem baumann_residual_supplement_of_normalClosure_top
    (S : Sylow 2 G)
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤) :
    pResidual 2 G ⊔ baumannSubgroup (S : Subgroup G) = ⊤ := by
  let B := baumannSubgroup (S : Subgroup G)
  let q := QuotientGroup.mk' (pResidual 2 G)
  have hq := QuotientGroup.mk'_surjective (pResidual 2 G)
  have hS : (S : Subgroup G).map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) (pResidual_sup_sylow_eq_top S)
    have hz : (pResidual 2 G).map q = ⊥ := by
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
    rwa [Subgroup.map_sup,hz,bot_sup_eq,map_top_of_surjective q hq] at hh
  let : (B.map q).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hS]
    exact (map_mono ((S : Subgroup G).le_normalizer.trans
      (normalizer_le_normalizer_baumannSubgroup _))).trans (B.le_normalizer_map q)
  have hB : B.map q = ⊤ := by
    have hh := congrArg (Subgroup.map q) hgen
    rw [map_normalClosure _ q hq,map_top_of_surjective q hq] at hh
    exact le_antisymm le_top (hh ▸ normalClosure_le_normal le_rfl)
  have hh := congrArg (Subgroup.comap q) hB
  rw [comap_map_eq,QuotientGroup.ker_mk',comap_top,sup_comm] at hh
  exact hh
/-- Actual normal generation supplies the escape premise and all opposite-generator conclusions. -/
theorem baumann_rank_one_opposites_of_generation
    (S : Sylow 2 G) (q : G →* Matrix.SpecialLinearGroup (Fin 2) F)
    (hq : Function.Surjective q) (hk : q.ker = pCore 2 G)
    (hgen : normalClosure (baumannSubgroup (S : Subgroup G) : Set G) = ⊤) :
    baumannSubgroup (S : Subgroup G) ⊔ pCore 2 G = (S : Subgroup G) ∧
    pResidual 2 G ⊔ baumannSubgroup (S : Subgroup G) = ⊤ ∧
    ∃ x : G, x ∈ pResidual 2 G ∧
      ((baumannSubgroup (S : Subgroup G) ⊔
        (baumannSubgroup (S : Subgroup G)).map (MulAut.conj x).toMonoidHom) ⊔
          pCore 2 G = ⊤) ∧
      omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊓
        (omegaCenterIn (thompsonSubgroup (S : Subgroup G))).map (MulAut.conj x).toMonoidHom =
        omegaCenterIn (thompsonSubgroup (S : Subgroup G)) ⊓ center G := by
  have hB : ¬ baumannSubgroup (S : Subgroup G) ≤ pCore 2 G := by
    intro hb
    have hh := normalClosure_le_normal hb
    rw [hgen,←hk] at hh
    have hqone : q = 1 := MonoidHom.ker_eq_top_iff.mp (top_unique hh)
    have hrtop := MonoidHom.range_eq_top.mpr hq
    rw [MonoidHom.range_eq_bot_iff.mpr hqone] at hrtop
    have hu : Matrix.SpecialLinearGroup.upperUnipotentHom F
        (Multiplicative.ofAdd (1 : F)) = 1 := by
      change _ ∈ (⊥ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
      rw [hrtop]
      trivial
    have hz := Matrix.SpecialLinearGroup.upperUnipotentHom_injective F
      (hu.trans (map_one (Matrix.SpecialLinearGroup.upperUnipotentHom F)).symm)
    exact one_ne_zero (congrArg Multiplicative.toAdd hz)
  obtain ⟨_,hS,x,hx,hopp⟩ := baumann_rank_one_generation S q hq hk hB
  exact ⟨hS,baumann_residual_supplement_of_normalClosure_top S hgen,x,hx,hopp,
    baumann_opposite_omega_intersection S hgen x hopp⟩
end Glauberman
