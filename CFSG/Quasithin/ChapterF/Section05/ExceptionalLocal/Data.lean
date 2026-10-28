module

public import CFSG.Quasithin.ChapterF.Section05.Source
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Literal subgroups in the exceptional F.5 branch

The two endpoint centralizers are intersections in the original ambient group.
Their two-cores and all residuals are mapped back by subgroup inclusions.
The groups `Dᵢ` are images of the fixed subgroups of the ordinary endpoints;
the graph involution is not adjoined to their definition. In particular the
normalizer quotient below is relative to its actual normalizer, not to `G`.

These definitions supply common interfaces for the F.4.37 fusion argument,
F.5.4 normalizer calculation and F.5.5 centralizer analysis. They impose no
structural or recognition conclusions.

Source: Aschbacher--Smith, F.4.37 and F.5.3--5, printed pp.293, 300--302.
-/

@[expose] public noncomputable section

namespace CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal

open Subgroup Theory.GroupTheory
open GreenBook.LieModels.UnitaryFour
open UnitaryTwo.GraphCentralizer

local notation "hn" => Nat.le_refl 1

/-- `false` is the point endpoint, `true` the plane endpoint. -/
def modelEndpoint : Bool → Type
  | false => Extension.point 1 hn
  | true => Extension.plane 1 hn

instance (b : Bool) : Group (modelEndpoint b) := by
  cases b <;> dsimp [modelEndpoint] <;> infer_instance

def ordinaryEndpoint : Bool → Type
  | false => pointParabolic 1 hn
  | true => planeParabolic 1 hn

instance (b : Bool) : Group (ordinaryEndpoint b) := by
  cases b <;> dsimp [ordinaryEndpoint] <;> infer_instance

/-- The actual ordinary-to-extended endpoint inclusion. -/
def ordinaryInclusion : (b : Bool) → ordinaryEndpoint b →* modelEndpoint b
  | false => Source.pointInclusion
  | true => Source.planeInclusion

/-- The same overlap involution viewed in either endpoint. -/
def modelGraph : (b : Bool) → modelEndpoint b
  | false => (Extension.amalgam 1 hn).left graphInvolution
  | true => (Extension.amalgam 1 hn).right graphInvolution

/-- Ordinary endpoint elements fixed by the marked graph involution. -/
def modelFixed (b : Bool) : Subgroup (ordinaryEndpoint b) :=
  (centralizer ({modelGraph b} : Set (modelEndpoint b))).comap (ordinaryInclusion b)

variable {G G0 : Type*} [Group G] [Group G0]
variable (c : RankTwoAmalgam.FaithfulCompletion (Extension.amalgam 1 hn) (G := G0))
  (i : G0 →* G)

def endpointMap : (b : Bool) → modelEndpoint b →* G
  | false => i.comp c.left
  | true => i.comp c.right

def ordinaryMap (b : Bool) : ordinaryEndpoint b →* G :=
  (endpointMap c i b).comp (ordinaryInclusion b)

/-- The source groups M₁ and M₂. -/
def M (b : Bool) : Subgroup G := (endpointMap c i b).range

/-- The actual full centralizer M_f. -/
def C : Subgroup G := centralizer ({Source.graphElement c i} : Set G)

/-- Eᵢ = C_{Mᵢ}(f), as an ambient subgroup. -/
def E (b : Bool) : Subgroup G := M c i b ⊓ C c i

/-- Aᵢ = O₂(Eᵢ), with the literal inclusion in G. -/
def A (b : Bool) : Subgroup G := (E c i b).pCoreIn 2

/-- Dᵢ is the image of C_{Gᵢ}(f) in the ordinary endpoint. -/
def Dendpoint (b : Bool) : Subgroup G := (modelFixed b).map (ordinaryMap c i b)

/-- The generated ordinary fixed group, without adjoining f. -/
def D : Subgroup G := Dendpoint c i false ⊔ Dendpoint c i true

/-- Qᵢ = O₂(O^{2′}(Gᵢ)), using the residual convention in F.4.31. -/
def Q (b : Bool) : Subgroup G :=
  (pCore 2 (primeToResidual 2 (ordinaryEndpoint b))).map
    ((ordinaryMap c i b).comp (primeToResidual 2 (ordinaryEndpoint b)).subtype)

/-- The Sylow candidate inside the actual involution centralizer. -/
def Tf : Subgroup (C c i) := (Source.sylowImage c i).subgroupOf (C c i)

/-- The same subgroup viewed in G. -/
def TfImage : Subgroup G := (Tf c i).map (C c i).subtype

/-- H = N_G(A₂). -/
def H : Subgroup G := normalizer (A c i true : Set G)

/-- The quotient uses Aᵢ as a normal subgroup of N_G(Aᵢ). -/
abbrev normalizerQuotient (b : Bool) :=
  normalizer (A c i b : Set G) ⧸ (A c i b).subgroupOf (normalizer (A c i b : Set G))

/-- A Sylow subgroup of C_G(f), retaining its inclusion in G. -/
def Rimage (R : Sylow 2 (C c i)) : Subgroup G :=
  (R : Subgroup (C c i)).map (C c i).subtype

/-- O²(D), included in the original ambient group. -/
def DtwoResidual : Subgroup G := (pResidual 2 (D c i)).map (D c i).subtype

/-- R₀ = C_R(O²(D)), as a subgroup of the original ambient group. -/
def Rzero (R : Sylow 2 (C c i)) : Subgroup G :=
  Rimage c i R ⊓ centralizer (DtwoResidual c i : Set G)

end CFSG.Quasithin.ChapterF.Section05.ExceptionalLocal
