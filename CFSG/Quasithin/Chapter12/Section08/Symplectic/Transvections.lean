module

public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Centralizer
public import CFSG.Quasithin.Chapter12.Section08.Symplectic.Transvections.Rank

/-!
# Lemma 12.8.11: full transvection action and exact rank

This proves clauses (3–5) for the literal marked subgroups, central quotient
U/Z(U), and faithful action quotient H/ker(uhatAction). The earlier source
inputs are the class-two bound, elementary central quotient, genuine
nondegenerate commutator form, V∩Z(U)=V₁, disjoint conjugate point line,
12.8.10(1),(6), elementary WX/E, and the action kernel E from 12.8.9(5).
All extra geometric premises of the intermediate transport theorems are
proved here; no transvection, fixed-space, order or rank conclusion is assumed.

The commutator form gives Z(X)=V₂Z(U)^g by double orthogonality. The exact
center cuts identify the common fixed space with V₂hat. Binary duality
then proves full action-image surjectivity, realizing each entire functional
by one element of X. Kernel cardinalities give the exact rank identity.
This uses the source 12.8.8(2) form in place of choosing E₀ and V₀ inside
an extraspecial factor, and proves separately that V₁^g maps onto V₂hat.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript (1 March 2004), Lemma 12.8.11(3–5), printed p.854 / PDF p.871.
The section assembly owner discharges all earlier §12.8 hypotheses.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

/-- The common fixed subspace inside the literal Ehat. -/
def EhatFixed (F : InvariantFlag T V n) [IsElementaryAbelian 2 F.Uhat]
    (g : G) : Submodule (ZMod 2) (Additive F.Uhat) :=
  hatSpace F (F.E g) ⊓ ⨅ x : dotImage F F.uhatAction (F.X g),
    ((linearAction F F.uhatAction x).toLinearMap - LinearMap.id).ker

/-- Source 12.8.11(4), with the exact common fixed subspace and marked plane.
The only assumptions beyond the marked flag are earlier §12.8 inputs. -/
theorem EhatFixed_eq_plane (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (g : G) (hg : g ∈ F.Gi 2) (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hZ : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) (hrefl : B.IsRefl) :
    EhatFixed F g = hatSpace F (F.Vi 2) := by
  have hcenter := center_X_eq_plane_sup_conjugate_ZU F g hg B hB hnd hrefl
  have hcut := E_plane_center_cuts F g hg hZ hZg
  ext e
  simp only [EhatFixed, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · rintro ⟨he,hfix⟩
    exact (Ehat_fixed_of_center_geometry F g hg hcomm hdis hcenter hcut ⟨e,he⟩).mp hfix
  · intro he
    have heE : e ∈ hatSpace F (F.E g) :=
      (map_mono (f := QuotientGroup.mk' (center F.U)) (comap_mono (plane_le_E F g hg)))
        (show e.toMul ∈ hatImage F (F.Vi 2) from he)
    exact ⟨heE, (Ehat_fixed_of_center_geometry F g hg hcomm hdis hcenter hcut ⟨e,heE⟩).mpr he⟩

/-- Source 12.8.11(3). The first inclusion says every actor is a transvection
with this center (possibly the identity); the reverse inclusion realizes each
entire functional by one actor, and the center is a proved nonzero line. -/
theorem full_transvection_action (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2)
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (hVZ : V ⊓ F.ZU = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hZ : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) (hrefl : B.IsRefl) :
    ∃ v : hatSpace F (F.E g), (v : Additive F.Uhat) ≠ 0 ∧
      Submodule.span (ZMod 2) {(v : Additive F.Uhat)} = hatSpace F (F.Vi 2) ∧
      (∀ x : dotImage F F.uhatAction (F.X g),
        ∃ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)), φ v = 0 ∧
          ∀ e : hatSpace F (F.E g), linearAction F F.uhatAction x e =
            (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat)) ∧
      (∀ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)), φ v = 0 →
        ∃ x : dotImage F F.uhatAction (F.X g),
          ∀ e : hatSpace F (F.E g), linearAction F F.uhatAction x e =
            (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat)) := by
  obtain ⟨v,hv,hline⟩ := exists_plane_hat_generator F hn g hg hVZ
  exact ⟨v,hv,hline,full_transvections_of_center_geometry F g hg hcomm hdis
    (center_X_eq_plane_sup_conjugate_ZU F g hg B hB hnd hrefl)
    (E_plane_center_cuts F g hg hZ hZg) v hv hline⟩

/-- Every prescribed transvection is realized by an element of the ORIGINAL X,
with the preliminary owner's literal action on U/Z(U). -/
theorem full_transvection_action_X (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2) (hX : F.X g ≤ F.H)
    (hcomm : ⁅F.U,F.U⁆ ≤ F.Vi 1) (hVZ : V ⊓ F.ZU = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hZ : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) (hrefl : B.IsRefl) :
    ∃ v : hatSpace F (F.E g), (v : Additive F.Uhat) ≠ 0 ∧
      Submodule.span (ZMod 2) {(v : Additive F.Uhat)} = hatSpace F (F.Vi 2) ∧
      ∀ φ : Module.Dual (ZMod 2) (hatSpace F (F.E g)), φ v = 0 →
        ∃ x : F.X g, ∀ e : hatSpace F (F.E g),
          Additive.ofMul (F.uhatAction (inclusion hX x) e.val.toMul) =
            (e : Additive F.Uhat) + φ e • (v : Additive F.Uhat) := by
  obtain ⟨v,hv,hline,_,hfull⟩ := full_transvection_action F hn g hg hcomm hVZ hdis hZ hZg B hB hnd hrefl
  refine ⟨v,hv,hline,fun φ hφ => ?_⟩
  obtain ⟨x,hx⟩ := hfull φ hφ
  obtain ⟨x,rfl⟩ := dotMap_surjective F F.uhatAction (F.X g) hX x
  exact ⟨x,hx⟩

/-- Source 12.8.11(5), using the exact earlier kernel and center-intersection
identities. Elementary abelianness, relative normality and the hyperplane
index are proved, not additional hypotheses. -/
theorem transvection_rank_identity (F : InvariantFlag T V n) [Finite G]
    [IsMulCommutative V] [IsElementaryAbelian 2 F.Uhat]
    (hn : 2 ≤ n) (g : G) (hg : g ∈ F.Gi 2)
    [((F.E g).subgroupOf (F.W ⊔ F.X g)).Normal]
    [IsElementaryAbelian 2 ((F.W ⊔ F.X g : Subgroup G) ⧸
      (F.E g).subgroupOf (F.W ⊔ F.X g))]
    (hVZ : V ⊓ F.ZU = F.Vi 1)
    (hdis : Disjoint (conjugate (F.Vi 1) g) F.ZU)
    (hZ : F.ZU ⊓ conjugate F.U g = (F.ZU ⊓ conjugate F.ZU g) ⊔ F.Vi 1)
    (hZg : conjugate F.ZU g ⊓ F.U =
      (F.ZU ⊓ conjugate F.ZU g) ⊔ conjugate (F.Vi 1) g)
    (hker : ∀ x : F.H, (x : G) ∈ F.X g →
      (F.uhatAction x = 1 ↔ (x : G) ∈ F.E g))
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (hB : ∀ u v : F.U, B (hatElement F u) (hatElement F v) = 0 ↔ Commute u v)
    (hnd : B.Nondegenerate) :
    let := Xdot_uhatAction_elementary F g hg
    primeRank 2 (hatImage F (F.E g)) + primeRank 2 (XdotCenterQuotient F F.uhatAction g) =
      primeRank 2 F.Uhat - 1 := by
  let := Xdot_uhatAction_elementary F g hg
  have hX : F.X g ≤ F.H := (F.X_le_plane_centralizer g hg).trans
    ((centralizer_le (F.monotone (by omega : 1 ≤ 2))).trans (centralizer_le_normalizer _))
  apply rank_identity_of_center_orders F g F.uhatAction hX
  · ext x
    exact hker (inclusion hX x) x.property
  · exact W_relIndex_U_eq_two F hn hVZ B hB hnd
  · exact card_E_inf_centers_eq F hn g hg hVZ hdis hZ hZg

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.Symplectic
