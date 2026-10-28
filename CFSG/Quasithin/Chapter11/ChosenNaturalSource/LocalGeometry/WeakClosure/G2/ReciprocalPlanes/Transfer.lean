module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes.Model
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.FixedSpaces

/-!
# Long-root planes on the original chosen G₂ cover

The original quotient intertwiner maps the actor's commutator space onto its
natural displacement plane. Pulling back that image adjoins exactly the original
central kernel. The same conjugation action embeds this binary commutator space
as the actual ambient group commutator. Thus [V,B] joined with C_V(L) is the full
marked plane preimage for every nontrivial actor inside a conjugate long root.
Conjugate applies this identity to the original reciprocal root actors.

Source: Aschbacher--Smith B.4.6 and 11.2.2(5), printed pp.88--90,768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open scoped commutatorElement IsMulCommutative

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
open Atlas.G2 Atlas.G2.Natural Atlas.G2.Natural.OrthogonalCover
open CFSG.Quasithin.ChapterB.QuasisimpleSource CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k:=ZMod 2) (g2Natural S.field.Carrier)))

private def subgroupSpace (B : Subgroup G) : Submodule (ZMod 2) D.space :=
  AddSubgroup.toZModSubmodule 2 (AddSubgroup.toSubgroup.symm
    (B.comap (V.subtype.comp D.spaceEquiv.toMonoidHom)))

private theorem coinvariants_range {H J X : Type*} [Group H] [Group J]
    [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (a : J →* H) :
    Coinvariants.ker (ρ.comp a) = Coinvariants.ker (ρ.comp a.range.subtype) := by
  apply le_antisymm <;> apply Submodule.span_le.mpr
  · rintro _ ⟨⟨x,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ:=ρ.comp a.range.subtype) ⟨a x,⟨x,rfl⟩⟩ v
  · rintro _ ⟨⟨⟨x,w,rfl⟩,v⟩,rfl⟩
    exact Coinvariants.sub_mem_ker (ρ:=ρ.comp a) w v

/-- A nontrivial root actor reconstructs the full plane preimage after adjoining
exactly the original covering center. The action is on the entire chosen module. -/
theorem root_commutator_sup_center (B : Subgroup G)
    (a : B →* Model S.field.Carrier) (u : Model S.field.Carrier)
    (hact : ∀ (x : B) (v : D.space),
      (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a x) v)) : G) =
        (x : G) * (D.spaceEquiv (Multiplicative.ofAdd v) : G) * (x : G)⁻¹)
    (ha : a.range ≤ LieParabolicSetup.highestRoot.map (MulAut.conj u).toMonoidHom)
    (hne : a.range ≠ ⊥) :
    ⁅V,B⁆ ⊔ (V ⊓ centralizer (L : Set G)) =
      (Coordinates.g2 m).preimage ((naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier u)) := by
  let σ : Representation (ZMod 2) B D.space := (Preliminary.markedAction D m).comp a
  let τ : Representation (ZMod 2) B (Natural.Space S.field.Carrier) := (restrictScalars (k:=ZMod 2) (Natural.action S.field.Carrier)).comp a
  let p : σ.IntertwiningMap τ :=
    (Preliminary.markedProjection D m).toLinearMap.intertwiningMap_of_isIntertwiningMap _ _
      (fun b v => LinearMap.congr_fun ((Preliminary.markedProjection D m).isIntertwining' (a b)) v)
  let P := (naturalPlane S.field.Carrier).map (Natural.action S.field.Carrier u)
  have hm : (Coinvariants.ker σ).map p.toLinearMap = P.restrictScalars (ZMod 2) := by
    rw [Representation.OneCohomology.map_coinvariants_of_surjective p (Preliminary.markedProjection_isCover D m).1]
    rw [coinvariants_range]
    exact root_coinvariants S.field.Carrier a.range u ha hne
  have hpre : (P.restrictScalars (ZMod 2)).comap p.toLinearMap =
      Coinvariants.ker σ ⊔ Preliminary.centralSpace D := by
    rw [←hm,Submodule.comap_map_eq]
    congr 1
    exact Preliminary.markedProjection_ker D m
  let X := ⁅V,B⁆ ⊔ (V ⊓ centralizer (L : Set G))
  have hcoinv : Coinvariants.ker σ ≤ subgroupSpace D X := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨b,v⟩,rfl⟩
    let j : Multiplicative D.space →* G := V.subtype.comp D.spaceEquiv.toMonoidHom
    change j (Multiplicative.ofAdd (Preliminary.markedAction D m (a b) v-v)) ∈ X
    rw [ofAdd_sub,map_div,div_eq_mul_inv]
    change (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a b) v)) : G) *
      (D.spaceEquiv (Multiplicative.ofAdd v) : G)⁻¹ ∈ X
    rw [hact]
    apply (show ⁅V,B⁆ ≤ X from le_sup_left)
    rw [commutator_comm]
    exact commutator_mem_commutator b.property (D.spaceEquiv (Multiplicative.ofAdd v)).property
  have hker : Preliminary.centralSpace D ≤ subgroupSpace D X := by
    intro v hv
    exact (show V ⊓ centralizer (L : Set G) ≤ X from le_sup_right)
      ⟨(D.spaceEquiv (Multiplicative.ofAdd v)).property,(Preliminary.mem_centralSpace_iff D v).mp hv⟩
  apply le_antisymm
  · apply sup_le
    · rw [commutator_comm]
      apply commutator_le.mpr
      intro b hb v hv
      let v' : V := ⟨v,hv⟩
      let w : D.space := (D.spaceEquiv.symm v').toAdd
      have hh : p (σ ⟨b,hb⟩ w-w) ∈ P := by
        change p (σ ⟨b,hb⟩ w-w) ∈ P.restrictScalars (ZMod 2)
        rw [←hm]
        exact Submodule.mem_map.mpr ⟨_,Coinvariants.sub_mem_ker (ρ:=σ) ⟨b,hb⟩ w,rfl⟩
      have hvp : (D.spaceEquiv (Multiplicative.ofAdd (σ ⟨b,hb⟩ w-w)) : G) ∈
          (Coordinates.g2 m).preimage P := by
        apply ((Coordinates.g2 m).mem_preimage P _).mpr
        change m.linearEquiv ((Preliminary.centralSpace D).mkQ
          (D.spaceEquiv.symm (D.spaceEquiv (Multiplicative.ofAdd (σ ⟨b,hb⟩ w-w)))).toAdd) ∈ P
        rw [D.spaceEquiv.symm_apply_apply]
        exact hh
      have he : (D.spaceEquiv (Multiplicative.ofAdd (σ ⟨b,hb⟩ w-w)) : G) = ⁅b,v⁆ := by
        rw [ofAdd_sub,map_div,Subgroup.coe_div,div_eq_mul_inv]
        change (D.spaceEquiv (Multiplicative.ofAdd (Preliminary.markedAction D m (a ⟨b,hb⟩) w)) : G) *
          (D.spaceEquiv (Multiplicative.ofAdd w) : G)⁻¹ = _
        rw [hact]
        simp only [w,ofAdd_toAdd,MulEquiv.apply_symm_apply]
        rfl
      exact he ▸ hvp
    · rw [←(Coordinates.g2 m).preimage_bot]
      exact ((Coordinates.g2 m).preimage_le_iff _ _).mpr bot_le
  · intro v hv
    let v' : V := ⟨v,D.centralQuotientPreimage_le _ hv⟩
    let w : D.space := (D.spaceEquiv.symm v').toAdd
    have hw : w ∈ (P.restrictScalars (ZMod 2)).comap p.toLinearMap :=
      ((Coordinates.g2 m).mem_preimage P v').mp hv
    rw [hpre] at hw
    have hh := (sup_le hcoinv hker) hw
    change (D.spaceEquiv (Multiplicative.ofAdd w) : G) ∈ X at hh
    simpa only [w,v',ofAdd_toAdd,MulEquiv.apply_symm_apply] using hh
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.ReciprocalPlanes
