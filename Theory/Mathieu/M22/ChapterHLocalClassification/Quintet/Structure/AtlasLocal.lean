module

public import Theory.AtlasPort.OtherSporadic.Mathieu.HexacodePointAlternating
public import Theory.AtlasPort.OtherSporadic.Mathieu.SextetSplitExtension

/-!
# The hexacode column kernel on a marked pair

The scalar of order three cycles the three nonzero letters. Together with
translations it matches any two distinct ordered points of a tetrad. Thus
any prescribed column permutation fixing that tetrad lifts while fixing the
marked pair pointwise. Conversely a column-kernel element preserving the pair
has trivial scalar component and is a translation.

These are the local affine calculations used in Aschbacher--Smith H.14.3(2),
printed p.397. The affine and scalar models reuse the ATLAS ports by Gerald
Höhn and ATLAS contributors, revision 8eabb35afe2b5e45bf913a2d05c53e558d2e2917,
under the ATLAS Research and Attribution License 1.0; see LICENSES/ATLAS.txt.
The finite checks below concern only the four-letter alphabet.
-/

@[expose] public section
noncomputable section
open Atlas.Codes
namespace Sporadic.Mathieu.M22ChapterH.Quintet.Structure
private theorem scalar_local_table :
    ∀ (i : HexIndex) (a b c d : Fin 4), a ≠ b → c ≠ d →
      ∃ (n : Fin 3) (t : Atlas.Codes.K),
        rowLabel.symm (((hexZ ^ n.val).val.localMap i) (rowLabel a) + t) = c ∧
        rowLabel.symm (((hexZ ^ n.val).val.localMap i) (rowLabel b) + t) = d := by
  decide +kernel

private theorem scalar_columns (n : ℕ) : hexCoordinateHom (hexZ ^ n) = 1 := by
  rw [map_pow, show hexCoordinateHom hexZ = 1 from rfl, one_pow]

/-- The column kernel matches any two ordered, distinct points in one tetrad. -/
theorem columnKernel_pair_transport (i : HexIndex) (a b c d : Fin 4)
    (hab : a ≠ b) (hcd : c ≠ d) :
    ∃ s : SextetStabilizer, (∀ j k, (s.val.val (j,k)).1 = j) ∧
      s.val.val (i,a) = (i,c) ∧ s.val.val (i,b) = (i,d) := by
  obtain ⟨n,t,ha,hb⟩ := scalar_local_table i a b c d hab hcd
  obtain ⟨v,hv⟩ := hexCoordinate_surjective i t
  have hp (j : HexIndex) : (hexZ ^ n.val).val.perm j = j :=
    Equiv.congr_fun (scalar_columns n.val) j
  refine ⟨sextetAffineEquiv ⟨Multiplicative.ofAdd v,hexZ ^ n.val⟩, ?_, ?_, ?_⟩
  · intro j k
    rw [sextetAffineEquiv_coordinates]
    exact hp j
  · rw [sextetAffineEquiv_coordinates, hp]
    change (_,rowLabel.symm (_ + v.val i)) = _
    change v.val i = t at hv
    rw [hv,ha]
  · rw [sextetAffineEquiv_coordinates, hp]
    change (_,rowLabel.symm (_ + v.val i)) = _
    change v.val i = t at hv
    rw [hv,hb]

/-- A prescribed column permutation fixing a tetrad lifts while fixing two of its points. -/
theorem atlas_pair_lift (i : HexIndex) (a b : Fin 4) (hab : a ≠ b)
    (σ : Equiv.Perm HexIndex) (hi : σ i = i) :
    ∃ s : SextetStabilizer, (∀ j k, (s.val.val (j,k)).1 = σ j) ∧
      s.val.val (i,a) = (i,a) ∧ s.val.val (i,b) = (i,b) := by
  obtain ⟨g,hg⟩ := hexCoordinateHom_surjective σ
  let s := sextetSection g
  have hp (j : HexIndex) (k : Fin 4) : (s.val.val (j,k)).1 = σ j := by
    change g.val.perm j = σ j
    exact Equiv.congr_fun hg j
  have he (k : Fin 4) : s.val.val (i,k) = (i,(s.val.val (i,k)).2) :=
    Prod.ext ((hp i k).trans hi) rfl
  have hn : (s.val.val (i,a)).2 ≠ (s.val.val (i,b)).2 := by
    intro h
    exact hab (Prod.mk.inj (s.val.val.injective (by rw [he a,he b,h]))).2
  obtain ⟨t,ht,ha,hb⟩ := columnKernel_pair_transport i _ _ a b hn hab
  refine ⟨t*s,?_,?_,?_⟩
  · intro j k
    change (t.val.val (s.val.val (j,k))).1 = σ j
    exact (ht (s.val.val (j,k)).1 (s.val.val (j,k)).2).trans (hp j k)
  · change t.val.val (s.val.val (i,a)) = _
    rw [he a,ha]
  · change t.val.val (s.val.val (i,b)) = _
    rw [he b,hb]

private theorem scalar_pair_free :
    ∀ (n : Fin 2) (i : HexIndex) (a b : Fin 4) (t : Atlas.Codes.K), a ≠ b →
      let f := fun k => rowLabel.symm
        (((hexZ ^ (n.val + 1)).val.localMap i) (rowLabel k) + t)
      (f a = a ∨ f a = b) → (f b = a ∨ f b = b) → False := by
  decide +kernel

/-- Fixing the columns and preserving a pair eliminates both nonidentity scalars. -/
theorem atlas_pair_kernel (i : HexIndex) (a b : Fin 4) (hab : a ≠ b)
    (s : SextetStabilizer) (hc : hexCoordinateHom (sextetQuotient s) = 1)
    (ha : s.val.val (i,a) = (i,a) ∨ s.val.val (i,a) = (i,b))
    (hb : s.val.val (i,b) = (i,a) ∨ s.val.val (i,b) = (i,b)) :
    sextetQuotient s = 1 := by
  obtain ⟨x,rfl⟩ := sextetAffineEquiv.surjective s
  rw [sextetQuotient_affine] at hc ⊢
  have exclude (n : Fin 2) (hr : x.right = hexZ ^ (n.val + 1)) : False := by
    have hp (j : HexIndex) : (hexZ ^ (n.val + 1)).val.perm j = j :=
      Equiv.congr_fun (scalar_columns _) j
    have he (k : Fin 4) : (sextetAffineEquiv x).val.val (i,k) =
        (i,rowLabel.symm (((hexZ ^ (n.val + 1)).val.localMap i) (rowLabel k) +
          x.left.toAdd.val i)) := by
      rw [sextetAffineEquiv_coordinates,hr,hp]
    rw [he a] at ha
    rw [he b] at hb
    exact scalar_pair_free n i a b (x.left.toAdd.val i) hab
      (ha.imp (fun h => (Prod.mk.inj h).2) (fun h => (Prod.mk.inj h).2))
      (hb.imp (fun h => (Prod.mk.inj h).2) (fun h => (Prod.mk.inj h).2))
  rcases hex_kernel_trichotomy x.right hc with h | h | h
  · exact h
  · exact (exclude 0 (by simpa using h)).elim
  · exact (exclude 1 h).elim


end Sporadic.Mathieu.M22ChapterH.Quintet.Structure
