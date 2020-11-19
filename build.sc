import mill._
import mill.scalalib._

object ulang extends ScalaModule {
    def scalaVersion = "2.12.12"

    def unmanagedClasspath = T {
        Agg.from(os.list(millSourcePath / "lib").map(PathRef(_)))
    }

    def ivyDeps = Agg(ivy"com.lihaoyi::sourcecode:0.2.0")
}
