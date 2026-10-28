module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.NonplaneOriginalFixedSelection

/-!
# The same smaller-mover selector fixes the original plane intersection

Retain the original maximizing plane as well as both selected planes.
In the contained-endpoint branch the generating triple already proves
that the original plane and the selected plane generate. In the nonplane
branch its marked central root proves the same assertion before the
endpoint is enlarged. The selector normalizes the original plane, so the
assertion holds for both choices in the same pair.

Transport the exact full-Z fixed subgroups of J and its plane. This gives
ambient fixedness for the intersection of the original mover's fixer
with either selected mover's fixer. No field degree or central attachment
is removed. These are the same selectors used in MS93 (5.6), supplying
the original-plane comparison needed in (5.11).
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Representation.OneCohomology
open Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource

private theorem conjugate_fixed_eq {G : Type*} [Group G]
    (Z J D : Subgroup G) (he : Z ⊓ centralizer (J : Set G) = Z ⊓ centralizer (D : Set G))
    (g : G) (hg : g ∈ normalizer (Z : Set G)) :
    Z ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set G) =
      Z ⊓ centralizer (D.map (MulAut.conj g).toMonoidHom : Set G) := by
  have hz := mem_normalizer_iff_map_conj_eq.mp hg
  change Z.map (MulAut.conj g).toMonoidHom = Z at hz
  have hh := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) he
  rw [map_inf _ _ _ (MulAut.conj g).injective,map_inf _ _ _ (MulAut.conj g).injective,
    Theory.GroupTheory.map_centralizer_equiv,Theory.GroupTheory.map_centralizer_equiv,hz] at hh
  exact hh

private theorem fixed_pair_of_equal_fixers {G : Type*} [Group G]
    (Z J J' D D' S : Subgroup G)
    (hJ : J ≤ S) (hJ' : J' ≤ S)
    (he : Z ⊓ centralizer (J : Set G)=Z ⊓ centralizer (D : Set G))
    (he' : Z ⊓ centralizer (J' : Set G)=Z ⊓ centralizer (D' : Set G))
    (hgen : D ⊔ D'=S) :
    (Z ⊓ centralizer (J : Set G)) ⊓ centralizer (J' : Set G)=
      Z ⊓ centralizer (S : Set G) := by
  apply le_antisymm
  · intro w hw
    have hwD := he ▸ hw.1
    have hwD' := he' ▸ (show w ∈ Z ⊓ centralizer (J' : Set G) from ⟨hw.1.1,hw.2⟩)
    refine ⟨hw.1.1,?_⟩
    have hD : D ≤ centralizer ({w} : Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hwD.2 y hy)
    have hD' : D' ≤ centralizer ({w} : Set G) :=
      fun y hy => mem_centralizer_singleton_iff.mpr (hwD'.2 y hy)
    intro y hy
    exact mem_centralizer_singleton_iff.mp ((sup_le hD hD') (hgen.symm ▸ hy))
  · exact fun w hw => ⟨⟨hw.1,centralizer_le hJ hw.2⟩,centralizer_le hJ' hw.2⟩

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Construct the same smaller-mover pair with its original-versus-selected
full-Z fixed identities, for every critical image size and the original
maximizing plane marking. -/
theorem Input.replacement_smaller_mover_original_fixed_selection
    {geometry : Geometry d.radical} {a z t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t) (hfirst : path.walk.getVert 1=t)
    (B : BinaryField) (hB : B.degree=n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype=Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hJplane : (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).subgroupOf (stabilizer d.radical a) ≤
        ((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f) :
    let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map
      (stabilizer d.radical a).subtype
    let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)
    ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
      let J₁ := J.map (MulAut.conj g).toMonoidHom
      let J₂ := J₁.map (MulAut.conj x⁻¹).toMonoidHom
      (J₁ ⊔ Z d.radical z) ⊔ (Z d.radical z).map (MulAut.conj x).toMonoidHom =
        stabilizer d.radical a ∧
      (D.map (MulAut.conj g).toMonoidHom ⊔
        (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom =
          stabilizer d.radical a) ∧
      ((Z d.radical a ⊓ centralizer (J₁ : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
      x ∈ (planeParabolic.comap f).map (stabilizer d.radical a).subtype ∧
      ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₁ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) ∧
      ((Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical))) ⊓
        centralizer (J₂ : Set (FreeAmalgam d.radical)) =
          Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) := by
  dsimp only
  let S := stabilizer d.radical a
  let D := (((CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype).comap f).map S.subtype
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  have hDS : D ≤ S := (map_le_range _ _).trans_eq (range_subtype _)
  have hJS : J ≤ S := (Subgroup.SmallMover.join_le _ _ _ _).trans
    (fun _ hx => hx.2 a (adjacent_symm _ hat))
  have hJD : J ≤ D := by
    have hh := map_mono (f := S.subtype) hJplane
    rwa [map_subgroupOf_eq_of_le hJS] at hh
  obtain ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,hop⟩ :
      ∃ g ∈ Ltilde d.radical a, ∃ x ∈ Ltilde d.radical a,
        (J.map (MulAut.conj g).toMonoidHom ⊔ Z d.radical z) ⊔
          (Z d.radical z).map (MulAut.conj x).toMonoidHom = S ∧
        (D.map (MulAut.conj g).toMonoidHom ⊔
          (D.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = S) ∧
        ((Z d.radical a ⊓ centralizer (J.map (MulAut.conj g).toMonoidHom : Set (FreeAmalgam d.radical))) ⊓
          centralizer ((J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom :
            Set (FreeAmalgam d.radical)) = Z d.radical a ⊓ centralizer (S : Set (FreeAmalgam d.radical))) ∧
        x ∈ normalizer (D : Set (FreeAmalgam d.radical)) ∧
        x ∈ (planeParabolic.comap f).map S.subtype ∧
        D ⊔ D.map (MulAut.conj g).toMonoidHom=S := by
    by_cases hc : ((Z d.radical z).subgroupOf S).map f ≤
        (CentralRootGeometry.wing (F := B.Carrier) true).map unipotent.subtype
    · obtain ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp⟩ :=
        h.replacement_smaller_mover_selection d path hb hat hfirst B hB f hf hfQ hTf hindex hJplane
      have hzD : Z d.radical z ≤ D := by
        have hh := map_mono (f := S.subtype) ((map_le_iff_le_comap).mp hc)
        rwa [map_subgroupOf_eq_of_le (path.endpoint_Z_le_start_stabilizer (by omega))] at hh
      have hzDx : (Z d.radical z).map (MulAut.conj x).toMonoidHom ≤ D :=
        (map_mono hzD).trans_eq (mem_normalizer_iff_map_conj_eq.mp hxn)
      have hDgS : D.map (MulAut.conj g).toMonoidHom ≤ S := by
        have hh := map_mono (f := (MulAut.conj g).toMonoidHom) hDS
        have hSg : S.map (MulAut.conj g).toMonoidHom=S :=
          mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (Ltilde_le_stabilizer a hg))
        exact hh.trans_eq hSg
      refine ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,le_antisymm (sup_le hDS hDgS) ?_⟩
      change stabilizer d.radical a ≤ _
      rw [←hgen]
      exact sup_le (sup_le ((map_mono hJD).trans le_sup_right) (hzD.trans le_sup_left))
        (hzDx.trans le_sup_left)
    · exact h.replacement_nonplane_original_plane_selection d path hb hat hfirst
        B hB f hf hfQ hTf hindex hc hJplane
  have hgS : g ∈ S := Ltilde_le_stabilizer a hg
  have hxS : x ∈ S := Ltilde_le_stabilizer a hx
  have hJ₁S : J.map (MulAut.conj g).toMonoidHom ≤ S :=
    (le_sup_left.trans le_sup_left).trans_eq hgen
  have hJ₂S : (J.map (MulAut.conj g).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom ≤ S := by
    have hh := map_mono (f := (MulAut.conj x⁻¹).toMonoidHom) hJ₁S
    have hSx : S.map (MulAut.conj x⁻¹).toMonoidHom=S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hxS))
    exact hh.trans_eq hSx
  have hop₂ : D ⊔ (D.map (MulAut.conj g).toMonoidHom).map
      (MulAut.conj x⁻¹).toMonoidHom=S := by
    have hh := congrArg (Subgroup.map (MulAut.conj x⁻¹).toMonoidHom) hop
    have hDx : D.map (MulAut.conj x⁻¹).toMonoidHom=D :=
      mem_normalizer_iff_map_conj_eq.mp ((normalizer (D : Set (FreeAmalgam d.radical))).inv_mem hxn)
    have hSx : S.map (MulAut.conj x⁻¹).toMonoidHom=S :=
      mem_normalizer_iff_map_conj_eq.mp (S.le_normalizer (S.inv_mem hxS))
    rw [Subgroup.map_sup,hDx,hSx] at hh
    exact hh
  have he := h.replacement_small_mover_parabolic_full_fixed d geometry hb path.start_color hat
    B hB f hf hfQ hindex hJplane
  have he₁ := conjugate_fixed_eq (Z d.radical a) J D he g (Z_normalized d.radical a hgS)
  have he₂ := conjugate_fixed_eq (Z d.radical a) _ _ he₁ x⁻¹
    (Z_normalized d.radical a (S.inv_mem hxS))
  exact ⟨g,hg,x,hx,hgen,hpair,hfixed,hxn,hxp,
    fixed_pair_of_equal_fixers _ _ _ _ _ _ hJS hJ₁S he he₁ hop,
    fixed_pair_of_equal_fixers _ _ _ _ _ _ hJS hJ₂S he he₂ hop₂⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
