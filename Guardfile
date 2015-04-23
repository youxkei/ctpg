# Add files and commands to this file, like the example:
#   watch(%r{file/path}) { `command(s)` }
#

pre_mtime = nil

guard :shell do
    watch %r{^(source|example)\/.*\.d$} do |files|
        mtime = File.new(files[0]).mtime
        msg = "\033[2J" + `dub test 2>&1` if pre_mtime != mtime
        pre_mtime = mtime
        msg
    end
end
